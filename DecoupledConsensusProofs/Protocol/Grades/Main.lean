module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Confirmation
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone
public import DecoupledConsensusInternal.Definitions.NamedResult23Statements
public import DecoupledConsensusInternal.Definitions.NamedStableChainOutage

@[expose] public section

/-! # P3(a) — the available chain at `t_GST = 0`
(`Props/Protocol.lean`; rev. 3 §8; PROTOCOL.md#the-complete-protocol)
`AvailableChainFrom` is three conclusions. This module says exactly where each
one stands.
* `ConfirmationMonotoneFrom` — **proved**, with no hypothesis at all
  (`Monotone.lean`).
* `ConfirmationCompatibleFrom` — proved **at one slot, at the store**; the
  trace-level and cross-slot steps are named residuals.
* `ProposalConfirmedFrom` — proved **at the store**; the trace-level reach and
  one-time `latest_confirmed` absorption steps are named residuals.
**The composed, genuine-or-nothing evaluation** (baseline `579000a`). §7's final
`update_confirmation` walks from `get_sg_root(Σ, round(Σ.s))` over
`get_filtered_block_tree(Σ)` and records the result only when it itself clears
the window gate; otherwise it records `get_fg_root(Σ)` — no confirmation
this slot. The reach premises of every store lemma here are therefore stated at
the **anchor and the candidate tree**, where the pre-rewire form stated them at
`Σ.F` and the live tree. The window sets are untouched, so `Confirmation.lean`
is consumed unchanged.
The two store-level theorems are the mathematical content and they are
unconditional given their store premises.
* `live_confirmed_eq` — the slot-`s` walk returns the honest proposal `B`
  exactly, and `B` clears the guard because the honest majority stands behind it
  (`HonestSupport.eligible` at `B` itself). `Confirmation.HonestSupport`
  supplies the three inputs `Walk.ghost_reaches` asks for: every ancestor of `B`
  clears the gate, every sibling of every such ancestor is strictly outscored,
  and no child of `B` clears the gate because a slot-`(s+1)` block carries no
  slot-`s` vote below it.
* `live_confirmed_compatible` — two slot-`s` evaluations that both **genuinely
  confirm** return compatible blocks, from counting and reach alone
  (`Confirmation.eligible_compatible`). The pre-rewire form needed each walk to
  have left its anchor, because eligibility of the result was only available off
  the anchor (`ghost_eligible`); the guard now supplies it outright, anchor
  included — the anchor-independent absorption the design records
  ( §9, "Confirmation-safety statement").
**What is not proved, and why it is named rather than hidden.**
1. `EvaluationReaches` — the trace-level bridge. It says that at `t_s + 6Δ` an
   honest node's recorded `Σ.live_confirmed` is the slot-`s` walk over a store
   meeting the store-level premises. Its **timestamp half is discharged**:
   `Sync.lean` has relay at `t_GST = 0` (`relay_gst_zero`) and both directions of
   the tick-grid bound (`processed_lt_of_store_time_lt` with
   `Proofs/Execution.lean`'s `stamp_is_last_tick`), so "held by `t_s + 2Δ`" and
   "stamped inside `early`" are interchangeable. What is **not** discharged is
   the step above it: that an honest voter's head at `t_s + Δ` is the honest
   proposal `B`. That is the §6 fork choice's own agreement argument — the
   merged view, the fresh/relative anchor and the filtered tree — and it is a
   separate proof from anything in this directory.
2. `ConfirmationAbsorbedAtEvaluation` — the one-time candidate-safety bridge.
   When all honest evaluations select the proposal as `Σ.live_confirmed`, each
   guarded `Σ.latest_confirmed` record must contain that proposal. The protocol
   step makes this a local consequence once the previous record and the candidate
   are comparable. The remaining run proof must establish that comparison; it
   must not be hidden inside a false claim that `Σ.live_confirmed` never
   retreats.
`LiveConfirmedNonRetreat` remains below as a separate healing and attestation
predicate. It is not a premise of `ProposalConfirmedFrom`: the public stable
record is `Σ.latest_confirmed`, whose future persistence follows from
`latest_confirmed_mono` after the one-time absorption above.
Both residuals are `Prop`s, and every theorem below is proved from them.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The confirmation evaluation, read off a store

`update_confirmation`'s four locals (PROTOCOL.md#the-complete-protocol), named so that the
counting lemmas of `Confirmation.lean` can be aimed at them. Every definition
here is `update_confirmation`'s own body, so `update_confirmation_live_confirmed`
is `rfl`. -/

/-- §7.2 `early`: the slot-`s` votes **resolved** before the support cutoff
(PROTOCOL.md#the-complete-protocol). The τ fold moved this set, and only this set, off the
receipt clock: `confLate` below still reads `Σ.timestamp[·]`, "whatever their
resolution". -/
def confEarly (E : Env V) (st : Protocol.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  beforeCutoff st.tau (Protocol.support_cutoff E s) (st.pool s)

/-- §7.2 `late`: the slot-`s` votes stamped before the evaluation
(PROTOCOL.md#the-complete-protocol). -/
def confLate (E : Env V) (st : Protocol.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (Protocol.confirmation_time E s) (st.pool s)

/-- §7.2 `support_votes`: the numerator (named `votes` before baseline
`7b2efec`). -/
def confVotes (E : Env V) (st : Protocol.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  (confEarly E st s).filter
    (fun u => Protocol.no_second_vote_in (confLate E st s) u = true)

/-- §7.2 `count`: the denominator (PROTOCOL.md#the-complete-protocol). -/
def confCount (E : Env V) (st : Protocol.Store V) (s : Slot) : Nat :=
  Protocol.voters_count E (confLate E st s) s

/-- §7.2 `score`: the **self-pair** — the numerator fills both walk arguments
(baseline `7b2efec`). -/
def confScore (E : Env V) (st : Protocol.Store V) (s : Slot) (B : Block V) : Nat :=
  Protocol.goldfish_score E st.T (confVotes E st s) (confVotes E st s) s B

/-- §7.2 `eligible`: the plain strict majority, with neither the current-slot
clause nor the height clause (PROTOCOL.md#the-complete-protocol). -/
def confEligible (E : Env V) (st : Protocol.Store V) (s : Slot) : Block V → Bool :=
  fun B => decide (confCount E st s < 2 * confScore E st s B)

/-- §7.2 `tree`: the candidate tree the composed walk descends
(PROTOCOL.md#the-complete-protocol). -/
def confTree (st : Protocol.Store V) : Finset (Block V) :=
  Protocol.get_filtered_block_tree st.toHealing.toFG

/-- §7.2 `root`: the fork-choice root — the value an unconfirmed slot records
(PROTOCOL.md#the-complete-protocol). -/
def confRoot (st : Protocol.Store V) : Block V :=
  Protocol.get_fg_root st.toHealing.toFG

/-- §7.2 `A`: the round's anchor (PROTOCOL.md#the-complete-protocol). -/
noncomputable def confAnchor (E : Env V) (hc : HealConfig) (st : Protocol.Store V) : Block V :=
  Protocol.get_sg_root E hc st.toHealing (hc.round_of st.s)


/-- §7.2 `A` under the contract the reading duty actually carries. `confAnchor`
is this at `GradeContract.current`; the named runtime reads its own prepared
frame instead, so every reach clause of the evaluation has to name the contract
(report §2.2: the anchor is the whole contract dependence of `live_confirmed`). -/
def confAnchorWith (contract : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) : Block V :=
  Protocol.get_sg_root_with contract E hc st.toHealing (hc.round_of st.s)

/-- §7.2 `H` under the same contract. Tree, score and gate are
profile-independent, so only the anchor argument moves. -/
def confWalkWith (contract : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) (s : Slot) : Block V :=
  Protocol.ghost (confAnchorWith contract E hc st) (confTree st) (confScore E st s)
    (confEligible E st s)


/-- The same guarded selection under an arbitrary grade contract. `rfl`, for the
same reason as the fixed-contract row: `update_confirmation_with` writes the
guard's value into the field and nothing else reads the contract. -/
theorem update_confirmation_with_live_confirmed (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).live_confirmed =
      if confEligible E st s (confWalkWith contract E hc st s) then
        confWalkWith contract E hc st s
      else confRoot st :=
  rfl


/-- The numerator of a real evaluation has the shape `Confirmation.lean` reasons
about: `early ⊆ late` (PROTOCOL.md#the-complete-protocol).

After the τ fold the inclusion needs two steps, not one. `early` is resolved
before `t_s + 2Δ` and `late` is *received* before `t_s + 6Δ`, so the argument is
`τ(u) < t_s + 2Δ ⟹ timestamp(u) < t_s + 2Δ ⟹ timestamp(u) < t_s + 6Δ` — the
resolution clock dominating the receipt clock, then the cutoff order. The
document's own sentence is unchanged and still true. -/
theorem confNumerator (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Numerator (confEarly E st s) (confLate E st s) (confVotes E st s) where
  early_late := by
    intro u hu
    rw [confEarly, beforeCutoff, Finset.mem_filter] at hu
    refine beforeCutoff_mono _ (support_cutoff_le_confirmation_time E s) _ ?_
    rw [beforeCutoff, Finset.mem_filter]
    exact ⟨hu.1, Protocol.stampedBefore_of_resolution hu.2⟩
  filtered := rfl

theorem confWalkWith_eq_of_support (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.Store V)
    (s : Slot) (Hon : Finset V) (B : Block V)
    (hsup : HonestSupport E st.T (confVotes E st s) s Hon B)
    (hvalid : Protocol.VoteSetValid E s (confLate E st s))
    (hpre : Block.Preceq (confAnchorWith contract E hc st) B)
    (hpath : ∀ C : Block V, Block.Preceq (confAnchorWith contract E hc st) C →
      C ≠ confAnchorWith contract E hc st → Block.Preceq C B → C ∈ confTree st) :
    confWalkWith contract E hc st s = B ∧ confEligible E st s B = true := by
  have hN := confNumerator E st s
  have hwalk : confWalkWith contract E hc st s = B := by
    refine ghost_reaches hpre hpath ?_ ?_
    · refine ghost_step_none ?_
      intro C _ hpar
      simp only [confEligible, decide_eq_false_iff_not, confCount, confScore]
      exact hsup.not_eligible hN hvalid (preceq_parent_false hpar)
    · intro H hanch hHB hne
      obtain ⟨C, hpar, hCB⟩ := exists_child_towards B hHB hne
      have hCA : Block.Preceq (confAnchorWith contract E hc st) C :=
        Block.preceq_trans hanch (preceq_of_parent? hpar)
      have hCne : C ≠ confAnchorWith contract E hc st := by
        intro hEq
        have h1 : C.depth = H.depth + 1 := depth_of_parent? hpar
        have h2 : (confAnchorWith contract E hc st).depth ≤ H.depth :=
          Block.preceq_depth_le hanch
        rw [hEq] at h1
        omega
      refine ⟨C, ?_, hCB⟩
      rw [Protocol.ghost_step]
      refine argmax?_eq_some_of_dominates ?_ ?_
      · rw [Protocol.ghost_children, Finset.mem_filter]
        refine ⟨hpath C hCA hCne hCB, hpar, ?_⟩
        simp only [confEligible, decide_eq_true_eq, confCount, confScore]
        exact hsup.eligible hN hvalid hCB
      · intro D hD hDC
        rw [Protocol.ghost_children, Finset.mem_filter] at hD
        have hDB : Block.preceq D B = false := by
          rw [← Bool.not_eq_true]
          intro hpre'
          exact hDC (child_towards_unique hpar hD.2.1 hCB hpre')
        simp only [confScore]
        exact hsup.score_lt hN hvalid hCB hDB
  have helig : confEligible E st s B = true := by
    simp only [confEligible, decide_eq_true_eq, confCount, confScore]
    exact hsup.eligible hN hvalid (Block.preceq_self B)
  exact ⟨hwalk, helig⟩

/-- **The slot-`s` evaluation confirms `B` exactly, under the contract the
reading duty carries.** Byte-for-byte the argument of `live_confirmed_eq`: the
anchor enters only as the walk's starting block, and `ghost_reaches`,
`ghost_step_none` and `argmax?_eq_some_of_dominates` all take it as a parameter.
Only the two reach premises and the guard row name the contract. -/
theorem live_confirmed_eq_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.Store V)
    (s : Slot) (Hon : Finset V) (B : Block V)
    (hsup : HonestSupport E st.T (confVotes E st s) s Hon B)
    (hvalid : Protocol.VoteSetValid E s (confLate E st s))
    (hpre : Block.Preceq (confAnchorWith contract E hc st) B)
    (hpath : ∀ C : Block V, Block.Preceq (confAnchorWith contract E hc st) C →
      C ≠ confAnchorWith contract E hc st → Block.Preceq C B → C ∈ confTree st) :
    (Protocol.update_confirmation_with contract E hc st s).live_confirmed = B := by
  obtain ⟨hwalk, helig⟩ :=
    confWalkWith_eq_of_support contract E hc st s Hon B hsup hvalid hpre hpath
  rw [update_confirmation_with_live_confirmed, hwalk, if_pos helig]


/-! ## Safety at the store: two slot-`s` evaluations agree -/




/-! ## The statement -/




end Protocol
end DecoupledConsensusModel

end
