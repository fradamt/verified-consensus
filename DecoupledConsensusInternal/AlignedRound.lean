module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Execution.Assumptions

@[expose] public section

/-!
# The aligned-round predicate — P4's hypothesis
(**rev. 4** §4; PROTOCOL.md#the-complete-protocol,
820–862, 1122–1200)

> **`AlignedRound(r)`** — at the instant round `r`'s action begins:
> **(a)** every honest validator emitted its round-`(r−1)` attestation;
> **(b)** the honest `live_confirmed` values lie on one chain — write `Can` for
> the deepest — and every honest round-`(r−1)` head is `⪯ Can` or empty;
> **(d′)** every nonempty target any honest validator emitted **before this
> instant** at a height `≥ h*` is compatible with `Can`;
> **(f)** every honest store has `Σ.h_max > h*`.

No recovery height, no `nj`, no debt: that story is P5's alone. The predicate is
a pure store-and-vote alignment property, and it is what makes P3(a) the round-0
instance of P4 (rev. 3 §6, unchanged by rev. 4).

## What rev. 4 changed, and why

Rev. 3 had six clause groups: (a), (b), **(c)** a common justification
`(Σ.h_j, Σ.J) = (h*, J)` with `J ⪯ Can`, (d) history alignment **above** `h*`,
and **(e)** no honest double vote. Rev. 4 deletes (c) and (e), extends (d) down
to `h*` itself, and adds (f).

**(c) is deleted because it was never load-bearing.** Every conclusion rev. 3
§4.4 draws from it — `Σ.J ⪯ Can`, `Σ.F ⪯ Can`, `get_fg_root ⪯ Can` — is
available from (d′) plus the two fault bounds, and the one thing (c) really bought
was *commonality*: that every honest store holds the **same** `(h*, J)`, which
no conclusion uses. What (c) was silently defending against was a late-revealed
justification or finalization off `Can` at or below `h*`, and the lex floor was
the defence. That defence is unnecessary:

* a **justification** at a height `≥ h*` off `Can` needs `2q − W` of honest
  weight signing an off-`Can` target there (Lemma G4), which is (d′) with the
  bound extended to `h*` — this is the whole reason (d′) reaches down to `h*`
  inclusive rather than stopping above it;
* a **finalization** at a height the canonical chain has crossed **violates the
  accountable fault bound** outright, by the quorum-clash argument
  (`Proofs.AlignedRoundLemmas.no_off_can_finalization`; corrected per rev. 4
  review): `Can`'s own chain carries a crossing quorum at that height, the two
  quorums intersect in `2q − W` of weight, and every member of the intersection
  signed a height pair and a finality pair at one height with different targets,
  which is **E1**. The intersection *is* the slashable weight, so
  `Execution.SlashableBound` rejects it directly — the argument counts no faulty
  weight, asks who is honest nowhere, and needs neither `BelowOneThird` nor
  `Proofs.SelfSafety.noPairSlashing`;
* a certificate **below** `h*` can lex-capture `Σ.J`, and rev. 3 read that as
  the reason for (c)'s floor. It is harmless without one: clause (f) makes the
  cascade gate `Σ.h_max = Σ.h_j + 1` unsatisfiable for such a certificate, so
  the gate never selects it, and the `F`-guard has nothing to accept by the
  previous item (`Proofs.AlignedRoundLemmas.sub_frontier_reveal_harmless`).

**(e) is deleted because it is a theorem.** It said no honest validator has
emitted two different targets at one height. That is now
`Proofs.AlignedRoundLemmas.honest_no_double_target`, proved outright over the
execution layer: `Λ.target` is write-once, every emitting row of `height_pair`
tests or sets it, `finality_pair` emits only under it, and a validator's record
is written by its own ticks alone. Rev. 3 stated it as a clause because the
run-level bridge from `Run.emits` to P2's `AttestHistory` did not exist; rev. 4
builds that bridge instead.

**(f) is new, and it is what replaces (c)'s floor.** `Σ.h_max > h*` is exactly
"the frontier has left `h*` behind", and it is the clause that makes the
sub-`h*` reveal of the previous paragraph inert. It is also strictly cheaper
than (c): `Σ.h_max` is raised by `update_finality`'s first line from any
processed block's state height, with no justification involved at all.

## Two shapes forced by Lean, both inherited from rev. 3

* `Round = ℕ`, so `r - 1` is truncated. The three round-`(r−1)` clauses carry an
  explicit `0 < r` guard, which is rev. 3 §6's "vacuous at round 0" made visible
  rather than accidental.
* (c⁺) is an existential over a quorum `Finset`, not `w.honest.filter (…)`. The
  emission predicate is an existential over the run and is not decidable, so it
  cannot index a `Finset.filter`.

**Every emission clause reads the run's past** (statement reviews, finding
O1 = C7; corrected per rev. 4 review, finding 6). `Run.emits` quantifies over the
whole event list, so a clause that neither guards nor pins its emission reads the
run's future; see `history`'s doc comment for what that costs. Two clauses carry
the guard `t < w.time` explicitly — `received` and `history`, and `history`'s is
the load-bearing one. The other three do not carry it and do not need it:
`emitted`, `heads` and (c⁺)'s `HonestOnly` all pin the emission with
`a.round = r - 1`, and `on_tick_emit` emits an attestation only at
`a_{a.round}`, so the emission sits at `a_{r−1} < a_r = w.time`. `emitted` and
`HonestOnly` are existentials, where a missing guard would only weaken the
hypothesis; `heads` is universally quantified over emissions, and there it is the
`a.round = r - 1` pin — not a guard — that keeps the clause in the past.

**`J` is no longer a parameter of the base predicate.** With (c) gone nothing in
(a), (b), (d′) or (f) names a justified block, so the justification is carried
only by `AlignedRoundPlus`, where (c⁺) needs it.
-/



namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every nonempty target an attestation carries at height `h`, in either pair
(PROTOCOL.md#the-complete-protocol). The empty pair and a timeout pair contribute nothing, so
"or the empty pair" needs no separate clause anywhere below. -/
def targetsAt (a : CombinedAttestation V) (h : Height) : Set BlockId :=
  {T | a.height_pair = HeightPair.target h T} ∪
    {T | a.finality_pair = some ⟨h, T⟩}

/-- `Can`: the deepest block confirmed by any honest validator, read off honest
stores alone (rev. 4 §4.2 clause (b)).

The second conjunct is both the "deepest" requirement and the one-chain
requirement: blocks with a common descendant are comparable, so `Can` being an
upper bound of the honest `live_confirmed` set is exactly what makes that set a
chain. -/
def IsCanonical (w : WorldView V) (Can : Block V) : Prop :=
  (∃ v ∈ w.honest, (w.state v).st.live_confirmed = Can) ∧
    (∀ v ∈ w.honest, Block.Preceq (w.state v).st.live_confirmed Can)

/-- **The aligned-round predicate at `a_r⁻`** (rev. 4 §4.2, §4.6). -/
structure AlignedRound (S : Setup V) (ρ : Run V) (r : Round) (Can : Block V)
    (h_star : Height) (w : WorldView V) : Prop where
  /-- **(a) Participation.** Every honest validator emitted its round-`(r−1)`
  attestation. Derivable in this layer from `tick_total` and post-GST relay, and
  stated anyway: it is what gives (b) content, because a validator that skipped
  round `r−1` still has a `latest` round further back whose head (b) does not
  constrain, and `majority_fork_choice` reads that head (rev. 3 §4.3). -/
  emitted : 0 < r → ∀ v ∈ w.honest, ∃ (a : NamedAttestation V) (t : Time),
    ρ.emits S v (Object.attest a) t ∧ a.round = r - 1
  /-- **(a) continued.** Every honest store holds all of them
  (PROTOCOL.md#the-complete-protocol).

  The `t < w.time` guard is the same one `history` carries and is content-free
  here: `on_tick_emit` emits an attestation only at `a_{a.round}`, so
  `a.round = r - 1` already pins the emission to `a_{r−1} < a_r`. It is stated so
  that every clause of this predicate reads the run's **past** and none of them
  can be falsified by extending the run. -/
  received : 0 < r → ∀ v ∈ w.honest, ∀ u ∈ w.honest,
    ∀ (a : NamedAttestation V) (t : Time), t < w.time →
      ρ.emits S u (Object.attest a) t →
      a.round = r - 1 → a.erase ∈ (w.state v).st.sg_pool (r - 1)
  /-- **(b) Confirmation alignment.** The honest `live_confirmed` values lie on
  one chain, and `Can` is the deepest of them. -/
  canonical : IsCanonical w Can
  /-- **(b) continued.** Every honest store holds `Can`. -/
  can_held : ∀ v ∈ w.honest, Can ∈ (w.state v).st.T
  
  heads : 0 < r → ∀ v ∈ w.honest, ∀ (a : NamedAttestation V) (t : Time),
    ρ.emits S v (Object.attest a) t → a.round = r - 1 →
      ∀ H, a.confirmed = some H →
        ∃ B ∈ (w.state v).st.T, B.root = H ∧ Block.Preceq B Can
  /-- **(d′) History alignment, down to `h*` inclusive.** Every nonempty target
  any honest validator has emitted **before this instant** at a height at or
  above `h*` — in a height pair or a finality pair — is compatible with `Can`.

  This is the only clause about the past, and it is exactly the history (a), (b)
  cannot see: an honest validator may have signed an off-canonical target at or
  above `h*` back when confirmations were not yet aligned. Stated in the
  target-compatibility form; the counting form is **false** in ordinary runs
  (rev. 3 §6).

  **Rev. 4 extends the bound from `h* < h` down to `h* ≤ h`**, which is what
  lets clause (c) go. Rev. 3 left the same-height case to Lemma U plus the
  deleted clause (e); the honest half of Lemma U is now proved
  (`Proofs.AlignedRoundLemmas.honest_no_double_target`), and the *canonicality*
  half at `h*` — that the height-`h*` justification is on `Can` at all — was
  what (c) supplied and nothing else did. Extending (d′) supplies it directly,
  and costs P5 nothing: the height `h*` is the frontier the recovery round
  itself justifies, so its honest targets are canonical by Lemma G1 in the same
  breath as those above it.

  **`t < w.time` is load-bearing.** `Run.emits` is an existential over the whole
  event list, so without the guard the clause reaches the run's *future* while
  the witness `∃ B ∈ (w.state v).st.T` is pinned to the store at `a_r⁻`. Round
  `r+k`'s honest target names a block created after `a_r`, which is in no store
  at `a_r⁻`, so the clause would be false in every run that makes progress —
  taking `AlignedRound(0)`, hence rev. 3 §6's base case and P3(a)-as-P4-at-0, and
  hence (C0) down with it. Future honest emissions are canonical by G1 + (b),
  which is (C2)'s job, not this clause's. -/
  history : ∀ v ∈ w.honest, ∀ (a : NamedAttestation V) (t : Time), t < w.time →
    ρ.emits S v (Object.attest a) t → ∀ h : Height, h_star ≤ h →
      ∀ T ∈ targetsAt a.erase h,
        ∃ B ∈ (w.state v).st.T, B.root = T ∧ Block.compatible B Can = true
  /-- **(f) The frontier has left `h*`.** Every honest store has
  `Σ.h_max > h*` (PROTOCOL.md#the-complete-protocol).

  New in rev. 4, and it is what replaces deleted clause (c)'s lex floor. Two
  uses, both in `Proofs.AlignedRoundLemmas`.

  * **It makes a sub-`h*` reveal inert.** `get_fg_root(Σ)` returns `Σ.J`
    only at `Σ.h_max = Σ.h_j + 1` (PROTOCOL.md#the-complete-protocol). A certificate at
    `h_j < h*` therefore cannot be selected while `Σ.h_max > h*`, whatever the
    lex order says about it — so the lex-capture attack rev. 3 §1.3 priced
    against Lemma U is excluded by the *gate*, not by the certificate's weight.
  * **It pins the gate-fires case to a height `≥ h*`.** When the gate does fire,
    `Σ.h_j = Σ.h_max − 1 ≥ h*`, so the selected justification's height is in
    (d′)'s range and its target is canonical.

  Cheap to establish and cheap to keep: `update_finality`'s first line raises
  `Σ.h_max` to `max(Σ.h_max, σ.h)` from any processed block, with no
  justification involved. The last line can lower it (F5.1), but only to the
  live tree's own maximum state height, which is at least `σ[Can].h` once `Can`
  is finalized-compatible — so (f) is preserved by the same argument that keeps
  `Can` viable (rev. 3 §4.4). -/
  frontier : ∀ v ∈ w.honest, h_star < (w.state v).st.h_max

/-- **(c⁺) Honest-only justification** (rev. 3 §4.5, restated for rev. 4). `h* =
0`, or the height-`h*` target quorum can be assembled from honest
round-`(r−1)` attestations alone.

**Rev. 4 note on `h*`.** Under rev. 3 the height was pinned by clause (c) as
"the common `Σ.h_j`"; with (c) gone, `h*` is a free parameter of the base
predicate and this clause names its own height and its own block explicitly.
Nothing else about (c⁺) changes.

Safety never uses it. P4-L does, and the reason is exact: `finality_pair` emits
`(h*, J)` only under `Λ.target[h*] = J` (PROTOCOL.md#the-complete-protocol), and by Lemma G3
the validators with that entry are precisely the height-`h*` target-vote
contributors. Under the base predicate alone honest contributors carry only
`≥ 2q − W < q`, so finality needs adversarial follow-through; under (c⁺) they
carry `≥ q`.

Deviation from rev. 3's sketch: an existential over a quorum `Finset` rather than
a `Finset.filter`, because the emission predicate is not decidable. -/
def HonestOnly (S : Setup V) (ρ : Run V) (r : Round) (h_star : Height) (J : Block V)
    (w : WorldView V) : Prop :=
  h_star = 0 ∨
    ∃ Q : Finset V, Q ⊆ w.honest ∧ S.E.q ≤ S.E.electorate.weightOf Q ∧
      ∀ v ∈ Q, ∃ (a : NamedAttestation V) (t : Time),
        ρ.emits S v (Object.attest a) t ∧ a.round = r - 1 ∧
          a.erase.height_pair = HeightPair.target h_star J.root

/-- The aligned round with (c⁺): P4-L's hypothesis (rev. 3 §4.5, §8; rev. 4 §4).

`J` rides on this structure rather than on the base predicate, because (c⁺) is
now the only clause that names a justified block. `just_can` is kept beside it:
P4-L's `L2Justifies` finalizes `h*` at `J`, and without the clause nothing says
that block is canonical — under rev. 3 the deleted clause (c) said it. -/
structure AlignedRoundPlus (S : Setup V) (ρ : Run V) (r : Round) (Can : Block V)
    (h_star : Height) (J : Block V) (w : WorldView V) : Prop extends
    AlignedRound S ρ r Can h_star w where
  /-- (c⁺). -/
  honest_only : HonestOnly S ρ r h_star J w
  /-- The justification (c⁺) names is on `Can`. **Carried, not derived** — P4-L
  is stated over the predicate, not over P4's proof — and the earlier note that
  (d′) plus root injectivity derives it was wrong twice (rev. 4 review,
  finding 5).

  * (c⁺)'s emission carries no `t < w.time` guard, while (d′) applies only to
    emissions before this instant. What bridges them is `a.round = r - 1` plus
    `on_tick_emit`, the argument `received`'s own comment gives — not root
    injectivity.
  * (d′) concludes `Block.compatible B Can`, and root injectivity identifies `B`
    with `J`. That is compatibility at `J`, not `J ⪯ Can`. The remaining step is
    a depth bound, the same one L1 carries as
    `Proofs.AlignedRoundLemmas.RootProvenance.just_depth`. -/
  just_can : Block.Preceq J Can


/-- W3's `GoodState` interface, filled by W1's predicate (design §5, §10;
rev. 4 §4.6). -/
def Good (S : Setup V) (ρ : Run V) (r : Round) : GoodState V :=
  fun w => ∃ (Can : Block V) (h_star : Height), AlignedRound S ρ r Can h_star w

end Internal
end DecoupledConsensusModel

end
