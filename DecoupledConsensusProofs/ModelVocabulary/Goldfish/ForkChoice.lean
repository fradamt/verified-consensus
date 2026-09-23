module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Env
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Objects
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Store
public import DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
public import DecoupledConsensusModel.Protocol.StoreBase

@[expose] public section

/-!
# §2.4 Goldfish fork choice
(PROTOCOL.md `sec:one-slot-ghost`, `def:goldfish-walk`, `alg:goldfish`)

`sec:one-slot-ghost`, `def:goldfish-walk`, `alg:goldfish`.

The pure core of the section: the score, the walk, the gate, and the two
compositions. `ghost` takes `score` and `eligible` as plain function arguments,
so the same walk serves the Goldfish fork choice, the §3 majority fork choice and
available confirmation (conventions: "pure core, thin stores").

Two model-forced parameters appear in front of the document's argument lists.

* `T`, the tree ancestry is resolved in. Votes name their target by root
  (modeling-choices row 12), so `B ⪯ B'` needs a tree to turn `vote.head` into
  `B'`. It is `Σ.T` at every §2 call site, and is kept separate from the `tree`
  the walk descends — the same split §3 states explicitly for `sg_support`
  (PROTOCOL.md `def:majority-fork-choice`,
  "still supports the child through which it descends").
* `cur`, the current slot `Σ.s`, read only by `goldfish_eligible`'s second
  clause.

The active counts quantify over every validator represented in the supplied
vote sets. Their `E` and `s` arguments remain in the public API so downstream
call sites do not need an unrelated signature migration. Committee membership
is enforced when a vote enters the pool, not repeated in these calculations.

The explicitly named `committee_*` definitions below retain the former
committee-filtered forms as proof helpers. They agree with the active raw forms
when the input is slot-uniform and every voter belongs to `K_s`.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Raw and committee-normalized counts

`votes_by`, `equivocates` and `participates` are in `Objects.lean`: §2.2 reads
them too.
-/

/-- The validity condition under which the source's ingress-validated raw vote
sets agree with the existing committee-normalized counting core. -/
def VoteSetValid (E : Env V) (s : Slot) (votes : Finset (GoldfishVote V)) : Prop :=
  ∀ u ∈ votes, u.slot = s ∧ u.val_index ∈ E.committee s

namespace VoteSetValid

/-- Validity is inherited by every subset. -/
theorem mono {E : Env V} {s : Slot} {votes support : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) (hsub : support ⊆ votes) :
    VoteSetValid E s support := by
  intro u hu
  exact hvalid u (hsub hu)

end VoteSetValid

/-- The active source-exact equivocator set.

`E` and `s` are compatibility parameters. Committee membership is checked at
vote-pool ingress and is not repeated here. -/
def equivocators (_E : Env V) (votes : Finset (GoldfishVote V)) (_s : Slot) :
    Finset V :=
  raw_equivocators votes

/-- The active source-exact participant set.

`E` and `s` are compatibility parameters. Committee membership is checked at
vote-pool ingress and is not repeated here. -/
def participants (_E : Env V) (votes : Finset (GoldfishVote V)) (_s : Slot) :
    Finset V :=
  raw_participants votes

/-- The former committee-filtered participant set, retained as a proof helper. -/
def committee_participants (E : Env V) (votes : Finset (GoldfishVote V))
    (s : Slot) : Finset V :=
  (E.committee s).filter (fun v => participates votes v = true)

/-- The former committee-filtered participant count, retained as a proof helper. -/
def committee_voters_count (E : Env V) (votes : Finset (GoldfishVote V))
    (s : Slot) : Nat :=
  (committee_participants E votes s).card

/-- The active source-exact supporter set.

`E` is a compatibility parameter. A validator with several qualifying votes
counts once. -/
def goldfishSupporters (_E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    Finset V :=
  raw_supporters T votes support_votes s B

/-! ## Raw/normalized equivalence -/

private theorem committee_of_mem_votes_by
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) {v : V} {u : GoldfishVote V}
    (hu : u ∈ votes_by votes v) : v ∈ E.committee s := by
  rw [votes_by, Finset.mem_filter] at hu
  have hc := (hvalid u hu.1).2
  simpa [hu.2] using hc

private theorem committee_of_participates
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) {v : V}
    (hv : participates votes v = true) : v ∈ E.committee s := by
  rw [participates, decide_eq_true_eq] at hv
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hv
  exact committee_of_mem_votes_by hvalid hu

private theorem committee_of_equivocates
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) {v : V}
    (hv : equivocates votes v = true) : v ∈ E.committee s := by
  rw [equivocates, decide_eq_true_eq] at hv
  have hpos : 0 < (votes_by votes v).card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  exact committee_of_mem_votes_by hvalid hu

/-- On a valid vote set, raw and committee-filtered participants agree. -/
theorem raw_participants_eq_committee_participants
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) :
    raw_participants votes = committee_participants E votes s := by
  ext v
  simp only [raw_participants, committee_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hv
    exact ⟨committee_of_participates hvalid hv, hv⟩
  · intro hv
    exact hv.2

/-- On a valid vote set, raw and committee-filtered voter counts agree. -/
theorem raw_voters_count_eq_committee_voters_count
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) :
    raw_voters_count votes = committee_voters_count E votes s := by
  rw [raw_voters_count, committee_voters_count,
    raw_participants_eq_committee_participants hvalid]

end Protocol
end DecoupledConsensusModel

end
