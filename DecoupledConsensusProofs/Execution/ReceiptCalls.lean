module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.ReceiptCallsGF
public import DecoupledConsensusProofs.Protocol.Schedule.ReceiptCallsF1

@[expose] public section

/-! A full processed-marker change in the actual event fold has an actual
handler origin. Carried origins use the checked recipient prefix calls; no
receipt, open or marker-origin premise is supplied by the network. -/
namespace DecoupledConsensusModel.Proofs.NamedReceiptCalls
open Execution
open Execution.NamedReceiptCalls
open NamedReceiptCallsBase
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem rows_bodies (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st a) rows).bodies = _
    rw [ih, NamedAdmission.admit_row_bodies]

private theorem block_bodies (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (C : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st C).bodies =
      (Protocol.NamedStore.process_block_core E hc cfg st C).bodies := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_bodies hc _ C.attestations
  · rfl

private theorem new_body_eq_input (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (C B : NamedBlock V)
    (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st C).bodies) :
    B = C := by
  rw [block_bodies] at hpost
  unfold Protocol.NamedStore.process_block_core at hpost
  split_ifs at hpost <;> first
    | exact False.elim (hpre hpost)
    | (dsimp only at hpost
       unfold Protocol.NamedStore.commitBlock at hpost
       split_ifs at hpost
       · exact (Finset.mem_insert.mp hpost).resolve_right hpre
       · exact False.elim (hpre hpost))



private theorem attest_bodies (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.bodies = st.bodies :=
  NamedAdmission.admit_row_bodies hc st _

private theorem tick_new_body_origin (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies) :
    NamedObject.block B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let due := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
  let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
  let st1 := if due then proposed.1 else st0
  let emitted1 : List (NamedObject V) := if due then
    match proposed.2 with | none => [] | some C => [.block C]
    else []
  let voteDue := 0 < s ∧ t = Protocol.vote_time E s
  let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
  let st2 := if voteDue then voted.1 else st1
  let emitted2 : List (NamedObject V) :=
    if voteDue then voted.2.toList.map NamedObject.gfVote else []
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have h32 : st3.bodies = st1.bodies := by
    dsimp only [st3, st2]
    split_ifs <;> rfl
  have hout := NamedTick.tick_computed_duties gc E hc cfg nd st record t
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      let a := Protocol.NamedDuties.attest_with gc E hc nd st3 record
      (a.1, a.2.1, emitted1 ++ emitted2 ++ [.attest a.2.2])
    else (st3, record, emitted1 ++ emitted2)) at hout
  have hbodies : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies = st1.bodies := by
    rw [hout]
    split_ifs
    · rw [attest_bodies, h32]
    · exact h32
  rw [hbodies] at hpost
  have hemit : ∀ o ∈ emitted1,
      o ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 := by
    intro o ho
    rw [hout]
    split_ifs <;> simp [List.mem_append, ho]
  by_cases hd : due
  · cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st0 with
    | none =>
      have he := NamedDuties.propose_none gc E hc cfg nd st0 hp
      exact False.elim (hpre (by simpa only [st1, proposed, if_pos hd, he] using hpost))
    | some C =>
      have he := NamedDuties.propose_some gc E hc cfg nd st0 C hp
      have hC : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st0 C).bodies := by
        simpa only [st1, proposed, if_pos hd, he] using hpost
      have hBC := new_body_eq_input E hc cfg st0 C B hpre hC
      subst B
      apply hemit (.block C)
      simp only [emitted1, proposed, if_pos hd, he, List.mem_singleton]
  · exact False.elim (hpre (by simpa only [st1, if_neg hd] using hpost))

private theorem new_vote_eq_input (E : Env V) (st : Protocol.Store V)
    (input u : GoldfishVote V) (hpre : u ∉ st.pool u.slot)
    (hpost : u ∈ (Protocol.on_goldfish_vote_checked E st input).pool u.slot) : input = u := by
  obtain ⟨j, hj, _⟩ := NamedReceiptCallsGF.fold_new_vote_origin E [input] st u hpre hpost
  exact (List.mem_singleton.mp (List.mem_of_getElem? hj)).symm

private theorem block_handled_of_change (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (B : NamedBlock V) (e : NamedEvent V)
    (he : rho.events[i]? = some e) (hv : e.node = v)
    (hpre : B ∉ (NamedRun.stateBefore S rho i v).st.bodies)
    (hpost : B ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies) :
    NamedRun.actualHandlesAtIndex S rho i v (.block B) := by
  cases e with
  | tick w t =>
    change w = v at hv
    subst w
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he] at hpost
    let n := NamedRun.stateBefore S rho i v
    let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
    have hb := tick_new_body_origin (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) n.st n.record t B hpre hpost
    exact Or.inl ⟨t, he, hb⟩
  | deliver w o t =>
    change w = v at hv
    subst w
    rw [delivery_result S rho he] at hpost
    cases o with
    | block C =>
      have hBC := new_body_eq_input S.E S.hc S.cfg _ C B hpre hpost
      subst C
      exact Or.inr ⟨t, he⟩
    | gfVote u => exact False.elim (hpre hpost)
    | attest a =>
      have hb : (NamedReceipt.process S (NamedRun.stateBefore S rho i v).st
          (.attest a)).bodies = (NamedRun.stateBefore S rho i v).st.bodies :=
        NamedAdmission.admit_row_bodies S.hc _ a
      exact False.elim (hpre (hb ▸ hpost))

private theorem gf_handled_of_change (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (u : GoldfishVote V) (e : NamedEvent V)
    (he : rho.events[i]? = some e) (hv : e.node = v)
    (hpre : u ∉ (NamedRun.stateBefore S rho i v).st.core.pool u.slot)
    (hpost : u ∈ (NamedRun.stateBefore S rho (i + 1) v).st.core.pool u.slot) :
    NamedRun.actualHandlesAtIndex S rho i v (.gfVote u) := by
  cases e with
  | tick w t =>
    change w = v at hv
    subst w
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he] at hpost
    let n := NamedRun.stateBefore S rho i v
    let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
    rcases NamedReceiptCallsGF.tick_new_vote_origin (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) n.st n.record t u hpre hpost with hem | ⟨B, hB, hp, hq⟩
    · exact Or.inl (Or.inl ⟨t, he, hem⟩)
    · have hcall := blockCallAt_self S rho he hB
      obtain ⟨j, hj⟩ := NamedReceiptCallsGF.block_with_new_vote_origin S rho i v B _ hcall u hp hq
      exact Or.inr ⟨B, j, _, hj⟩
  | deliver w o t =>
    change w = v at hv
    subst w
    rw [delivery_result S rho he] at hpost
    cases o with
    | block B =>
      obtain ⟨j, hj⟩ := NamedReceiptCallsGF.block_with_new_vote_origin S rho i v B _
        (blockCallAt_delivery S rho he) u hpre hpost
      exact Or.inr ⟨B, j, _, hj⟩
    | gfVote input =>
      have hi := new_vote_eq_input S.E _ input u hpre hpost
      subst input
      exact Or.inl (Or.inr ⟨t, he⟩)
    | attest a =>
      have hg := (NamedAdmission.admit_row_fixed_fields S.hc
        (NamedRun.stateBefore S rho i v).st a).2.2.2.2.1
      have hp : u ∈ (NamedRun.stateBefore S rho i v).st.core.pool u.slot := by
        simpa only [NamedReceipt.process, Protocol.Store.pool, hg] using hpost
      exact False.elim (hpre hp)

private theorem row_handled_of_change (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (a : NamedAttestation V) (e : NamedEvent V)
    (he : rho.events[i]? = some e) (hv : e.node = v)
    (hpre : a ∉ (NamedRun.stateBefore S rho i v).st.sg_rows a.round)
    (hpost : a ∈ (NamedRun.stateBefore S rho (i + 1) v).st.sg_rows a.round) :
    NamedRun.actualHandlesAtIndex S rho i v (.attest a) := by
  cases e with
  | tick w t =>
    change w = v at hv
    subst w
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he] at hpost
    let n := NamedRun.stateBefore S rho i v
    let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
    rcases NamedReceiptCallsF1.tick_new_full_row_origin (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) n.st n.record t a hpre hpost with hem | ⟨B, hB, hp, hq⟩
    · exact Or.inl (Or.inl ⟨t, he, hem⟩)
    · have hcall := blockCallAt_self S rho he hB
      obtain ⟨j, hj, _, _⟩ := NamedReceiptCallsF1.block_full_marker_origin
        S rho i v B _ a hcall hp hq
      exact Or.inr ⟨B, j, _, hj⟩
  | deliver w o t =>
    change w = v at hv
    subst w
    exact (NamedReceiptCallsF1.delivered_row_accepts S rho i v o t a he hpre hpost).1.1

/-- A new full marker produces its actual event and handler origin for every
object kind. It is not assumed to have been received or admitted elsewhere. -/
theorem new_marker_accepts (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (o : NamedObject V)
    (hpre : NamedReceipt.processed (NamedRun.stateBefore S rho i v).st o = false)
    (hpost : NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) v).st o = true) :
    ∃ t : Time, NamedRun.acceptsAt S rho i v o t := by
  cases he : rho.events[i]? with
  | none =>
    rw [Proofs.NamedRuntime.stateBefore_succ, he] at hpost
    change NamedReceipt.processed (NamedRun.stateBefore S rho i v).st o = true at hpost
    rw [hpre] at hpost
    cases hpost
  | some e =>
    have hv : e.node = v := by
      by_contra hne
      rw [Proofs.NamedRuntime.stateBefore_other S rho he v (Ne.symm hne), hpre] at hpost
      cases hpost
    have hcall : NamedRun.actualHandlesAtIndex S rho i v o := by
      cases o with
      | block B =>
        exact block_handled_of_change S rho i v B e he hv
          (by simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpre)
          (by simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost)
      | gfVote u =>
        exact gf_handled_of_change S rho i v u e he hv
          (by simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpre)
          (by simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost)
      | attest a =>
        exact row_handled_of_change S rho i v a e he hv
          (by simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpre)
          (by simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost)
    exact ⟨e.time, ⟨hcall, e, he, hv, rfl⟩, hpre, hpost⟩

theorem new_block_accepts (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (hpre : B ∉ (NamedRun.stateBefore S rho i v).st.bodies)
    (hpost : B ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies) :
    ∃ t : Time, NamedRun.acceptsAt S rho i v (.block B) t :=
  new_marker_accepts S rho i v (.block B)
    (by simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpre)
    (by simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost)


theorem new_attestation_accepts (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (a : NamedAttestation V) (hpre : a ∉ (NamedRun.stateBefore S rho i v).st.sg_rows a.round)
    (hpost : a ∈ (NamedRun.stateBefore S rho (i + 1) v).st.sg_rows a.round) :
    ∃ t : Time, NamedRun.acceptsAt S rho i v (.attest a) t :=
  new_marker_accepts S rho i v (.attest a)
    (by simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpre)
    (by simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost)

#print axioms new_marker_accepts
#print axioms new_block_accepts
#print axioms new_attestation_accepts
end DecoupledConsensusModel.Proofs.NamedReceiptCalls

end
