module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedAdmissible
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedReceiptCalls
public import DecoupledConsensusInternal.Definitions.ActionSources

@[expose] public section

/-!
# SG pool provenance under carried admission 

The wire-only equalities `on_block_sg_votes` and `on_block_checked_sg_votes`
are false under F1 and are retired to prior. The cone keeps three facts in
their place: the pool only grows along a run (unchanged shape), every new
pooled row at a block event is a row carried by that block (checked in
`NamedF1Interactions`), and an honest signer's row in any honest pool is
that signer's own action row (restated over the named run through the two
admission paths, wire and carried, both authenticated).
-/


namespace DecoupledConsensusModel.Internal.PoolProvenance
open Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Q-P1: the projected pool and the full row bucket only grow along a run. -/
def PoolMonotoneQuery (S : Setup V) (rho : Run V) : Prop :=
  ∀ v (r : Round) (i j : Nat), i ≤ j →
    (NamedRun.stateBefore S rho i v).st.sg_pool r ⊆ (NamedRun.stateBefore S rho j v).st.sg_pool r ∧
    (NamedRun.stateBefore S rho i v).st.namedPool r ⊆ (NamedRun.stateBefore S rho j v).st.namedPool r

/-- Q-P2: at a block event, every newly pooled full row is carried by that block
(the erased pool gains only projections of such rows). -/
def BlockEventPoolDeltaQuery (S : Setup V) (rho : Run V) : Prop :=
  ∀ (i : Nat) v (B : NamedBlock V) t, rho.events[i]? = some (.deliver v (.block B) t) →
    ∀ a : NamedAttestation V,
      a ∈ (NamedRun.stateBefore S rho (i + 1) v).st.namedPool a.round →
      a ∈ (NamedRun.stateBefore S rho i v).st.namedPool a.round ∨ a ∈ B.attestations

/-- Q-P3: honest row provenance, both admission paths. An honest validator's
full row found in any honest node's bucket is that validator's actual action
row of the bucket round, and it was emitted at that action. This is the named
restatement of `honestSGVote_actionEmission_of_mem_storeBeforeTime`; the
premise set is `NamedAdmissibleCore` (authentic, causal), nothing more. -/
def HonestRowProvenanceQuery (S : Setup V) (rho : Run V) : Prop :=
  NamedAdmissibleCore S rho →
  ∀ (w v : V) (time : Time) (k : Round) (a : NamedAttestation V),
    v ∈ rho.honest → a.val_index = v →
    a ∈ (NamedRun.stateBeforeTime S rho time w).st.namedPool k →
    a.round = k ∧ a = actionAttestationAt S rho v k ∧
      NamedRun.emits S rho v (.attest (actionAttestationAt S rho v k)) (S.a k)

/-- Q-P4: the projected form used by the relative-majority selector. -/
def HonestProjectionProvenanceQuery (S : Setup V) (rho : Run V) : Prop :=
  NamedAdmissibleCore S rho →
  ∀ (w v : V) (time : Time) (k : Round) (u : Protocol.SGVote V),
    v ∈ rho.honest → u.val_index = v →
    u ∈ (NamedRun.stateBeforeTime S rho time w).st.core.toHealing.sg_votes k →
    u = Protocol.sgVote (actionAttestationAt S rho v k).erase

/-- Q-P5: delivery form, wire path (the named twin of `attest_pooled_of_delivery`). -/
def WireDeliveryPooledQuery (S : Setup V) (rho : Run V) : Prop :=
  NamedAdmissibleCore S rho →
  ∀ (w : V) (i : Nat) (a : NamedAttestation V) (t' : Time),
    w ∈ rho.honest → a.val_index ∈ rho.honest →
    rho.events[i]? = some (.deliver w (.attest a) t') →
    (∃ s, NamedRun.emits S rho a.val_index (.attest a) s) →
    S.a a.round ≤ t' → t' < S.a a.round + S.E.Δ →
    a ∈ (NamedRun.stateBefore S rho (i + 1) w).st.namedPool a.round

/-- Q-P6: delivery form, carried path: an honest row carried by a block that
is freshly processed inside the same bracket is pooled at the block event. -/
def CarriedDeliveryPooledQuery (S : Setup V) (rho : Run V) : Prop :=
  NamedAdmissibleCore S rho →
  ∀ (w : V) (i : Nat) (B : NamedBlock V) (a : NamedAttestation V) (t' : Time),
    w ∈ rho.honest → a.val_index ∈ rho.honest → a ∈ B.attestations →
    rho.events[i]? = some (.deliver w (.block B) t') →
    B ∉ (NamedRun.stateBefore S rho i w).st.bodies →
    B ∈ (NamedRun.stateBefore S rho (i + 1) w).st.bodies →
    (∃ s, NamedRun.emits S rho a.val_index (.attest a) s) →
    S.a a.round ≤ t' → t' < S.a a.round + S.E.Δ →
    a ∈ (NamedRun.stateBefore S rho (i + 1) w).st.namedPool a.round

/-- Q-P7: the action read preserves the projected pool (twin of
`actionStoreAt_projectedSGVotes`): the confirmation duty writes no vote. -/
def ActionReadPoolQuery (S : Setup V) (rho : Run V) : Prop :=
  ∀ w r, (actionReadAt S rho w r).st.core.toHealing.sg_votes =
    (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.sg_votes

end DecoupledConsensusModel.Internal.PoolProvenance

end
