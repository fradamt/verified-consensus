module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.BlockVisibilityCore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalTransportCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Execution.Acceptance
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks
public import DecoupledConsensusProofs.Protocol.Handlers.CommitteePools
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Run producer for confirmation adoption

This module discharges the execution side of `Protocol.AdoptionTransport`
at the two final Section 7 reads. A slot-`s` confirmation reads
`Proofs.Optimistic.confStore` at `t_s + 6Δ`; an ordinary slot-`(s+1)` vote reads
`Proofs.Optimistic.voteDutyStore` at `t_s + 5Δ`. The confirmation numerator is
resolved before `t_s + 2Δ`, and the ordinary raw/support pair freezes at
`t_s + 3Δ`.

Block delivery is admission-scoped. `ResolvedTargetsAdmittedBefore` therefore
states the receiver-side liveness premise explicitly: every block that resolves
a counted source vote is admitted at the target before the freeze. The lemmas
below turn that premise into target membership and root resolution by using the
run's block-stamp invariant and collision-free hash model.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



/-! ## Schedule identities -/

/-- One delivery interval after the support cutoff is the view freeze. -/
theorem support_cutoff_add_delta_eq_view_freeze (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s + E.Δ = Protocol.view_freeze E s := by
  unfold Protocol.support_cutoff Protocol.view_freeze
  ring

/-- The slot-`s` view freeze precedes the next vote duty. -/
theorem view_freeze_lt_vote_time_succ (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.vote_time E (s + 1) := by
  have key : ∀ a d : Int, 0 < d → a + 3 * d < a + 5 * d := by
    intro a d hd
    omega
  have hrw : Protocol.vote_time E (s + 1) = E.t s + 5 * E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    push_cast
    ring
  rw [hrw]
  exact key (E.t s) E.Δ E.Δ_pos

/-- One delivery interval after the next vote duty is the slot-`s`
confirmation time. -/
theorem vote_time_succ_add_delta_eq_confirmation_time (E : Env V) (s : Slot) :
    Protocol.vote_time E (s + 1) + E.Δ = Protocol.confirmation_time E s := by
  unfold Protocol.vote_time Protocol.confirmation_time Env.t slotStart
  push_cast
  ring

/-- A vote relayed one interval after the ordinary view freeze still arrives
strictly before the confirmation read. -/
theorem view_freeze_add_delta_lt_confirmation_time (E : Env V) (s : Slot) :
    Protocol.view_freeze E s + E.Δ < Protocol.confirmation_time E s := by
  have key : ∀ a d : Int, 0 < d → a + 3 * d + d < a + 6 * d := by
    intro a d hd
    omega
  exact key (E.t s) E.Δ E.Δ_pos

/-- An instant from the slot start up to the confirmation read belongs to slot
`s` or slot `s+1`. -/
theorem slotOf_of_proposal_before_confirmation (E : Env V) (s : Slot) {p : Time}
    (hlo : Protocol.proposal_time E s ≤ p)
    (hhi : p < Protocol.confirmation_time E s) :
    E.slotOf p = s ∨ E.slotOf p = s + 1 := by
  by_cases hnext : p < Protocol.proposal_time E (s + 1)
  · apply Or.inl
    have hbounds : ∀ a d q : Int, 0 < d → a ≤ q → q < a + 4 * d →
        0 ≤ q - a ∧ q - a < 4 * d := by
      intro a d q hd h1 h2
      omega
    have hstart : Protocol.proposal_time E (s + 1) = E.t s + 4 * E.Δ := by
      unfold Protocol.proposal_time Env.t slotStart
      push_cast
      ring
    have hnext' : p < E.t s + 4 * E.Δ := by rwa [hstart] at hnext
    obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlo hnext'
    have hrw : p = 4 * E.Δ * (s : Time) + (p - E.t s) := by
      unfold Env.t slotStart
      ring
    rw [Env.slotOf, hrw]
    exact Proofs.Optimistic.slotOfTime_add E.Δ E.Δ_pos s _ h0 h1
  · apply Or.inr
    have hlonext : Protocol.proposal_time E (s + 1) ≤ p := le_of_not_gt hnext
    have hbounds : ∀ a d q : Int, 0 < d → a + 4 * d ≤ q → q < a + 6 * d →
        0 ≤ q - (a + 4 * d) ∧ q - (a + 4 * d) < 4 * d := by
      intro a d q hd h1 h2
      omega
    have hstart : Protocol.proposal_time E (s + 1) = E.t s + 4 * E.Δ := by
      unfold Protocol.proposal_time Env.t slotStart
      push_cast
      ring
    have hlonext' : E.t s + 4 * E.Δ ≤ p := by rwa [hstart] at hlonext
    obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlonext' hhi
    have hrw : p = 4 * E.Δ * ((s + 1 : Slot) : Time) +
        (p - (E.t s + 4 * E.Δ)) := by
      unfold Env.t slotStart
      push_cast
      ring
    rw [Env.slotOf, hrw]
    exact Proofs.Optimistic.slotOfTime_add E.Δ E.Δ_pos (s + 1) _ h0 h1


/-- A delivery after the slot start and before its confirmation read sees slot
`s` or slot `s+1` in the receiver store. -/
theorem delivery_store_slot_before_confirmation
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {o : Object V} {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver w o t))
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s) :
    (rho.stateBefore S i w).st.s = s ∨ (rho.stateBefore S i w).st.s = s + 1 := by
  have htick : Event.tick w (Protocol.proposal_time S.E s) ∈ rho.events :=
    adm.tick_total w hw _ (Proofs.Optimistic.publicTime_proposal_time S s)
      (Proofs.Optimistic.proposal_time_nonneg S.E s)
      (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hclock : Protocol.proposal_time S.E s ≤ (rho.stateBefore S i w).st.t :=
    tick_le_store_time S adm.toNamedScheduleWellFormed hi htick hlo
  have hup : (rho.stateBefore S i w).st.t ≤ t := by
    simpa [Event.time] using store_time_le_event_time S adm.toNamedScheduleWellFormed hi w
  have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i w
  unfold Proofs.Optimistic.SlotOfClock at hslot
  show (rho.stateBefore S i w).st.core.s = s ∨ (rho.stateBefore S i w).st.core.s = s + 1
  rw [hslot]
  exact slotOf_of_proposal_before_confirmation S.E s hclock
    (lt_of_le_of_lt hup hhi)

/-! ## One-handler vote settlement -/

omit [Fintype V] in
/-- At a store whose slot-window guards are open, processing a Goldfish vote
before `Γ` either records that exact vote before `Γ` or leaves two timely votes
by the same validator. The second arm is the protocol's two-vote cap.

This lemma does not use honesty. It is the local handler fact needed after an
accepted-forwarding delivery of a Byzantine or honest confirmation supporter. -/
theorem on_goldfish_vote_beforeCutoff_or_equivocates
    (st : Protocol.Store V) (u : GoldfishVote V) (Γ : Time)
    (hstamps : PoolStamps st)
    (hfresh : ¬ u.slot < st.s - 1) (hfuture : ¬ st.s < u.slot)
    (hclock : st.t < Γ) :
    u ∈ beforeCutoff (Protocol.on_goldfish_vote st u).timestamp_vote Γ
        ((Protocol.on_goldfish_vote st u).pool u.slot) ∨
      Protocol.equivocates
        (beforeCutoff (Protocol.on_goldfish_vote st u).timestamp_vote Γ
          ((Protocol.on_goldfish_vote st u).pool u.slot)) u.val_index = true := by
  by_cases hdup : u ∈ st.gf_votes u.slot
  · have heq : Protocol.on_goldfish_vote st u = st := by
      unfold Protocol.on_goldfish_vote
      rw [if_pos (Or.inr (Or.inr hdup))]
    rw [heq]
    apply Or.inl
    rw [beforeCutoff, Finset.mem_filter, Protocol.Store.pool, List.mem_toFinset]
    refine ⟨hdup, ?_⟩
    obtain ⟨c, hc⟩ : ∃ c : Stamp, st.timestamp_vote u = some c :=
      Option.isSome_iff_exists.mp (hstamps.stamped u.slot u hdup)
    simp only [stampedBefore, hc, decide_eq_true_eq]
    exact lt_of_le_of_lt (hstamps.bounded u c hc) (WithBot.coe_lt_coe.mpr hclock)
  by_cases hequiv : Protocol.equivocates (st.pool u.slot) u.val_index = true
  · have heq : Protocol.on_goldfish_vote st u = st := by
      unfold Protocol.on_goldfish_vote
      rw [if_neg (by aesop), if_pos hequiv]
    rw [heq]
    apply Or.inr
    rw [Protocol.equivocates, decide_eq_true_eq] at hequiv ⊢
    have hsub : Protocol.votes_by (st.pool u.slot) u.val_index ⊆
        Protocol.votes_by
          (beforeCutoff st.timestamp_vote Γ (st.pool u.slot)) u.val_index := by
      intro x hx
      rw [Protocol.votes_by, Finset.mem_filter] at hx ⊢
      refine ⟨?_, hx.2⟩
      rw [beforeCutoff, Finset.mem_filter]
      refine ⟨hx.1, ?_⟩
      rw [Protocol.Store.pool, List.mem_toFinset] at hx
      obtain ⟨c, hc⟩ : ∃ c : Stamp, st.timestamp_vote x = some c :=
        Option.isSome_iff_exists.mp (hstamps.stamped u.slot x hx.1)
      simp only [stampedBefore, hc, decide_eq_true_eq]
      exact lt_of_le_of_lt (hstamps.bounded x c hc) (WithBot.coe_lt_coe.mpr hclock)
    exact lt_of_lt_of_le hequiv (Finset.card_le_card hsub)
  · have hguards : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨
        u ∈ st.gf_votes u.slot) := by
      aesop
    obtain ⟨hgf, hts, -⟩ := on_goldfish_vote_insert st u hguards (by simpa using hequiv)
    apply Or.inl
    rw [beforeCutoff, Finset.mem_filter, Protocol.Store.pool, List.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [hgf]
      simp
    · rw [hts]
      simp only [ite_true, stampedBefore, decide_eq_true_eq]
      exact WithBot.coe_lt_coe.mpr hclock

/-- The source-exact checked ingress has the same settlement result for a vote
from its slot committee. -/
theorem on_goldfish_vote_checked_beforeCutoff_or_equivocates
    (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) (Γ : Time)
    (hcommittee : u.val_index ∈ E.committee u.slot)
    (hstamps : PoolStamps st)
    (hfresh : ¬ u.slot < st.s - 1) (hfuture : ¬ st.s < u.slot)
    (hclock : st.t < Γ) :
    u ∈ beforeCutoff
          (Protocol.on_goldfish_vote_checked E st u).timestamp_vote Γ
          ((Protocol.on_goldfish_vote_checked E st u).pool u.slot) ∨
      Protocol.equivocates
        (beforeCutoff
          (Protocol.on_goldfish_vote_checked E st u).timestamp_vote Γ
          ((Protocol.on_goldfish_vote_checked E st u).pool u.slot))
        u.val_index = true := by
  have hcheck : ¬ (u.val_index ∉ E.committee u.slot) := by
    intro hnot
    exact hnot hcommittee
  rw [Protocol.on_goldfish_vote_checked, if_neg hcheck]
  exact on_goldfish_vote_beforeCutoff_or_equivocates st u Γ hstamps
    hfresh hfuture hclock

omit [Fintype V] in
/-- Equivocation detection is monotone in the vote set. -/
theorem equivocates_mono {A B : Finset (GoldfishVote V)} (hAB : A ⊆ B) (x : V)
    (hA : Protocol.equivocates A x = true) :
    Protocol.equivocates B x = true := by
  rw [Protocol.equivocates, decide_eq_true_eq] at hA ⊢
  have hsub : Protocol.votes_by A x ⊆ Protocol.votes_by B x := by
    intro u hu
    rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
    exact ⟨hAB hu.1, hu.2⟩
  exact le_trans hA (Finset.card_le_card hsub)

omit [Fintype V] in
/-- A pool carry preserves every strict receipt-cutoff view. -/
theorem beforeCutoff_subset_of_poolCarry {st st' : Protocol.Store V}
    (hcarry : PoolCarry st st') (k : Slot) (Γ : Time) :
    beforeCutoff st.timestamp_vote Γ (st.pool k) ⊆
      beforeCutoff st'.timestamp_vote Γ (st'.pool k) := by
  intro u hu
  rw [beforeCutoff, Finset.mem_filter, Protocol.Store.pool, List.mem_toFinset] at hu ⊢
  refine ⟨hcarry.mem k u hu.1, ?_⟩
  cases hc : st.timestamp_vote u with
  | none => rw [stampedBefore, hc] at hu; simp at hu
  | some c =>
      simp only [stampedBefore, hc, decide_eq_true_eq] at hu
      simp only [stampedBefore, hcarry.stamp u c hc, decide_eq_true_eq]
      exact hu.2

/-- Folding the checked ingress settles a committee-valid target vote. Other
votes in the carried list can be outside their committees; the checked handler
rejects them without changing the pool, stamp map, slot, or clock. -/
theorem foldl_on_goldfish_vote_checked_beforeCutoff_or_equivocates
    (E : Env V) (st : Protocol.Store V) (l : List (GoldfishVote V))
    (u : GoldfishVote V) (Γ : Time)
    (hcommittee : u.val_index ∈ E.committee u.slot)
    (hstamps : PoolStamps st) (hu : u ∈ l)
    (hfresh : ¬ u.slot < st.s - 1) (hfuture : ¬ st.s < u.slot)
    (hclock : st.t < Γ) :
    u ∈ beforeCutoff
          (l.foldl (Protocol.on_goldfish_vote_checked E) st).timestamp_vote Γ
          ((l.foldl (Protocol.on_goldfish_vote_checked E) st).pool u.slot) ∨
      Protocol.equivocates
        (beforeCutoff
          (l.foldl (Protocol.on_goldfish_vote_checked E) st).timestamp_vote Γ
          ((l.foldl (Protocol.on_goldfish_vote_checked E) st).pool u.slot))
        u.val_index = true := by
  induction l generalizing st with
  | nil => simp at hu
  | cons x xs ih =>
      rw [List.mem_cons] at hu
      rcases hu with hxu | hu
      · subst x
        have hlocal := on_goldfish_vote_checked_beforeCutoff_or_equivocates
          E st u Γ hcommittee hstamps hfresh hfuture hclock
        have hstep := (poolStep_on_goldfish_vote_checked E st u) hstamps
        have htail := (poolStep_foldl_on_goldfish_vote_checked E xs
          (Protocol.on_goldfish_vote_checked E st u)) hstep.2
        rw [List.foldl_cons]
        rcases hlocal with hmem | hequiv
        · exact Or.inl (beforeCutoff_subset_of_poolCarry htail.1 u.slot Γ hmem)
        · apply Or.inr
          apply equivocates_mono _ u.val_index hequiv
          exact beforeCutoff_subset_of_poolCarry htail.1 u.slot Γ
      · rw [List.foldl_cons]
        have hstep := (poolStep_on_goldfish_vote_checked E st x) hstamps
        apply ih (Protocol.on_goldfish_vote_checked E st x) hstep.2 hu
        · simpa only [Proofs.Optimistic.on_goldfish_vote_checked_slot] using hfresh
        · simpa only [Proofs.Optimistic.on_goldfish_vote_checked_slot] using hfuture
        · simpa only [on_goldfish_vote_checked_time] using hclock

/-- A vote that settles before the slot-`s` freeze is visible in the next
ordinary two-view pair. Exact receipt plus head admission gives support;
the cap arm gives raw-view equivocation. -/
theorem settled_before_freeze_in_voter_pair
    (E : Env V) (st : Protocol.Store V) (s : Slot) {u : GoldfishVote V}
    {H : Block V} (hfind : Block.find? st.T u.head = some H)
    (hH : stampedBefore st.timestamp_block (Protocol.view_freeze E s) H = true)
    (hslot : H.slot ≤ u.slot)
    (hsettled :
      u ∈ beforeCutoff st.timestamp_vote (Protocol.view_freeze E s) (st.pool s) ∨
        Protocol.equivocates
          (beforeCutoff st.timestamp_vote (Protocol.view_freeze E s) (st.pool s))
          u.val_index = true) :
    u ∈ Protocol.voter_support_view E st.toHealing.toFG.toSG.toGoldfishStore (s + 1) ∨
      Protocol.equivocates
        (Protocol.voter_view E st.toHealing.toFG.toSG.toGoldfishStore (s + 1)) u.val_index = true := by
  rcases hsettled with hrecv | hequiv
  · apply Or.inl
    apply Proofs.Optimistic.mem_voter_support_view_of_pool E st.toHealing.toFG.toSG.toGoldfishStore (s + 1)
    rw [Nat.add_sub_cancel]
    apply Proofs.Optimistic.mem_tau_cutoff_of hrecv
    · exact hfind
    · exact hslot
    · exact hH
  · apply Or.inr
    apply equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [Protocol.voter_view]
    apply Finset.mem_union_left
    rw [Nat.add_sub_cancel]
    exact hx

/-! ## Direct forwarding deliveries -/



/-! ## Backward forwarding into the confirmation late view -/

/-- A standalone vote delivery after the slot start and before the confirmation
read settles in that read's receipt-cutoff view. -/
theorem gfVote_delivery_settled_at_confStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {u : GoldfishVote V}
    {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver w (Object.gfVote u) t))
    (hus : u.slot = s)
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.confirmation_time S.E s) :
    u ∈ confLate S.E (Proofs.Optimistic.confStore S rho w s) s ∨
      Protocol.equivocates
        (confLate S.E (Proofs.Optimistic.confStore S rho w s) s) u.val_index = true := by
  let pre := (rho.stateBefore S i w).st.core
  have hslot : pre.s = s ∨ pre.s = s + 1 :=
    delivery_store_slot_before_confirmation S adm hw hi hlo hhi
  have hclock : pre.t < Protocol.confirmation_time S.E s :=
    lt_of_le_of_lt
      (by simpa [pre, Event.time] using
        store_time_le_event_time S adm.toNamedScheduleWellFormed hi w)
      hhi
  have hfresh : ¬ u.slot < pre.s - 1 := by
    rcases hslot with hs | hs
    · rw [hus, hs]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    · rw [hus, hs, Nat.add_sub_cancel]
      exact Nat.lt_irrefl s
  have hfuture : ¬ pre.s < u.slot := by
    rcases hslot with hs | hs
    · rw [hus, hs]
      exact Nat.lt_irrefl s
    · rw [hus, hs]
      exact Nat.not_lt.mpr (Nat.le_add_right s 1)
  have hcommittee : u.val_index ∈ S.E.committee u.slot := by
    have hwire := adm.wire i w (Object.gfVote u) t hi
    simpa only [Object.wellFormed, NamedReceipt.wellFormed, Protocol.vote_well_formed,
      decide_eq_true_eq] using hwire
  have hlocal := on_goldfish_vote_checked_beforeCutoff_or_equivocates
    S.E pre u (Protocol.confirmation_time S.E s) hcommittee
    (poolStamps_stateBefore S adm.toNamedScheduleWellFormed w i)
    hfresh hfuture hclock
  have hpost : (rho.stateBefore S (i + 1) w).st.core =
      Protocol.on_goldfish_vote_checked S.E pre u := by
    rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hi]
    rfl
  let Γ := Protocol.confirmation_time S.E s
  let N := (rho.events.filter (fun e => decide (e.time < Γ))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hΓt : Γ ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Γ)
        (j := i) (e := Event.deliver w (Object.gfVote u) t)
        (by simpa [N] using hNle) hi
    exact (not_le_of_gt hhi) hΓt
  have hcarry : PoolCarry (rho.stateBefore S (i + 1) w).st.core
      (rho.stateBefore S N w).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed w N (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.confStore S rho w s =
      Proofs.Optimistic.tickStore S (rho.stateBefore S N w).st.core Γ := by
    unfold Proofs.Optimistic.confStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Γ) w)]
  have hfields :
      (Proofs.Optimistic.confStore S rho w s).timestamp_vote =
          (rho.stateBefore S N w).st.core.timestamp_vote ∧
        (Proofs.Optimistic.confStore S rho w s).gf_votes =
          (rho.stateBefore S N w).st.core.gf_votes := by
    rw [hstore]
    exact ⟨rfl, rfl⟩
  rw [← hpost] at hlocal
  rw [hus] at hlocal
  rcases hlocal with hmem | hequiv
  · apply Or.inl
    rw [confLate, hfields.1, Protocol.Store.pool, hfields.2]
    exact beforeCutoff_subset_of_poolCarry hcarry s Γ hmem
  · apply Or.inr
    apply equivocates_mono _ u.val_index hequiv
    intro x hx
    rw [confLate, hfields.1, Protocol.Store.pool, hfields.2]
    exact beforeCutoff_subset_of_poolCarry hcarry s Γ hx



/-! ## Accepted carrier settlement -/










/-- If the target already holds a vote immediately after the source acceptance
event, its frozen receipt view at the later vote duty contains that vote. This
is the `already accepted` branch of typed forwarding. -/
theorem gfVote_processed_after_event_at_voteDuty
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {i : Nat} {e : Event V} {u : GoldfishVote V} {s : Slot}
    (he : rho.events[i]? = some e) (hus : u.slot = s)
    (hprocessed : Object.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = true)
    (hearly : e.time < Protocol.view_freeze S.E s) :
    u ∈ beforeCutoff
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
      (Protocol.view_freeze S.E s)
      ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) := by
  have hmem : u ∈ (rho.stateBefore S (i + 1) w).st.gf_votes s := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq, Protocol.Store.pool,
      List.mem_toFinset] at hprocessed
    rwa [hus] at hprocessed
  have hstamps := poolStamps_stateBefore S adm.toNamedScheduleWellFormed w (i + 1)
  obtain ⟨c, hc⟩ : ∃ c : Stamp,
      (rho.stateBefore S (i + 1) w).st.timestamp_vote u = some c :=
    Option.isSome_iff_exists.mp (hstamps.stamped s u hmem)
  have hclock : (rho.stateBefore S (i + 1) w).st.t ≤ e.time :=
    block_store_time_after_event_le S adm.toNamedScheduleWellFormed he w
  have hcFreeze : c < (Protocol.view_freeze S.E s : Stamp) :=
    lt_of_le_of_lt (hstamps.bounded u c hc)
      (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock hearly))
  let Γ := Protocol.vote_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Γ))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hΓe : Γ ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed (t := Γ)
        (j := i) (e := e) (by simpa [N] using hNle) he
    exact (not_le_of_gt
      (lt_trans hearly (view_freeze_lt_vote_time_succ S.E s))) hΓe
  have hcarry : PoolCarry (rho.stateBefore S (i + 1) w).st.core
      (rho.stateBefore S N w).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed w N (Nat.succ_le_of_lt hiN)
  have hstore : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (rho.stateBefore S N w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Γ) w)]
  rw [hstore]
  rw [beforeCutoff, Finset.mem_filter, Protocol.Store.pool, List.mem_toFinset]
  refine ⟨hcarry.mem s u hmem, ?_⟩
  simp only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, stampedBefore,
    hcarry.stamp u c hc, decide_eq_true_eq]
  exact hcFreeze


/-! ## Admission-scoped target preservation -/







/-! ## Forward field from accepted forwarding -/

/-- The event-indexed acceptance window for a confirmation numerator.

The membership and acceptance provenance are theorems (`confVotes` is a pool
subset and `acceptsAt_gfVote_of_processed` finds the first acceptance). The
two time inequalities are the remaining stamp-to-handler-time bridge: the
future-slot guard supplies the lower bound, and the numerator's resolution
stamp supplies the strict upper bound. -/
def ConfirmationVotesAcceptedInWindow (S : Setup V) (rho : Run V) (v : V)
    (source : Protocol.Store V) (s : Slot) : Prop :=
  ∀ u ∈ confVotes S.E source s,
    ∃ (i : Nat) (t : Time), NamedRun.acceptsAt S rho i v (Object.gfVote u) t ∧
      u.slot = s ∧ Protocol.proposal_time S.E s ≤ t ∧
      t < Protocol.support_cutoff S.E s



/-! ## Backward field and complete constructor -/



/-- Acceptance timing for the receipt-cutoff arm of the target raw view. This
is the same stamp-to-first-handler theorem needed by confirmation numerators,
instantiated at the view-freeze cutoff. -/
def TargetReceiptVotesAcceptedInWindow (S : Setup V) (rho : Run V) (w : V)
    (s : Slot) : Prop :=
  ∀ u ∈ beforeCutoff
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
      (Protocol.view_freeze S.E s)
      ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s),
    ∃ (i : Nat) (t : Time), NamedRun.acceptsAt S rho i w (Object.gfVote u) t ∧
      u.slot = s ∧ Protocol.proposal_time S.E s ≤ t ∧
      t < Protocol.view_freeze S.E s









end Protocol
end DecoupledConsensusModel

end
