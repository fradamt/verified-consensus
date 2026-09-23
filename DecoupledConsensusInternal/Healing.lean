module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Recurrence
public import DecoupledConsensusInternal.Optimistic
public import DecoupledConsensusInternal.Derived

@[expose] public section

/-!
# P5 healing — the aligned round is reached
(design note P5; rev. 3 §7, §8;
PROTOCOL.md#the-complete-protocol)

The aligned-round predicate says nothing about a recovery height. The causal
story that it becomes true *because of* one is P5's, and it is the project's
three-phase argument:

> the `nj` gap pins the root at the recovery height; a justification for `H+1`
> **is** healing — grade safety makes exiting the recovery height synonymous with
> healed, and liveness was the only question; post-heal, confirmation safety ⇒
> justification safety ⇒ reveals are root-forward moves along the canonical
> chain.

The third clause is P4's (C0) and (C3). The first two are P5's, and they are why
the statement carries a **nonfinality-run** side condition.

**Why the side condition** (rev. 3 §7.3). `nj` is chain-relative through `h_F`,
and `advance_height` recomputes it from the transition's own post-finality `h_F`
(PROTOCOL.md#the-complete-protocol). Under sustained nonfinality the relativity collapses:
if no chain state anywhere records a finalized height above `h_F⁰`, then every
branch has `h_F ≤ h_F⁰` at every height, so `h − h_F ≥ h − h_F⁰` and
`h − h_F⁰ > D` implies `nj` on **every** branch. Only the one-sided bound is
needed — a branch that lags is *more* nonjustifiable, which is the safe
direction — so the recovery heights are globally uniform and phase (i) applies
with no per-branch hypothesis. No protocol change is implied: `nj` stays
chain-relative, as defined. doc2's trichotomy is the strengthening, at the cost
of a bound linear in the number of late-revealed finalized heights.

**Why the fault bound is P5's too** (rev. 4; amended per rev. 4 review). P5
carries `BelowOneThird` rather than `HonestQuorum`, and it takes two separate
arguments to get there: one for *some* bound, one for *this* bound.

**Some bound is necessary.** No recovery statement is available above one third
of *slashable* weight. Two conflicting finalizations `F` and `F′` can both be
assembled there, and
`update_finality`'s admission guard is `σ.F ⪯ Σ.J` with `Σ.F` monotone
(PROTOCOL.md#the-complete-protocol) — so an honest validator that admitted `F` can never
afterwards accept anything conflicting with it. The honest set is partitioned
permanently, clause (b) of the predicate is false in every later round, and no
bound of any size makes the conclusion true. The bound is a hypothesis of the
theorem because it is a hypothesis of the fact.

**And it must be the adversarial one** (design notes §4, rev. 4 §13.3). The
paragraph above argues only that *a* bound is needed, and the object it argues
against — two conflicting finalizations at one height — is `2q − W` of E1
evidence, so it is an argument for the **accountable** `SlashableBound`. That is
not the bound P5 carries, and the reason it is not is this: clearing the prior
justifications means **crossing** heights, crossing needs a progress quorum, and
a progress quorum is `q` weight of **actual participation** — fresh votes at a
height nobody has voted at, which conflict with nothing and are therefore
unslashable. `SlashableBound` bounds only the faults that leave evidence, so it
says nothing about how much weight votes at all; only `3 · w(faulty) < W`
guarantees the honest weight a progress quorum needs. In the user's words,
*progress is necessary to regain safety even.* There is no weak-form variant of
P5, and everything downstream of its hand-off inherits the strong bound.

**Stability is not P5's problem.** P4 carries (C0), so P5 needs the predicate at
a **single** round. Stating it "for all later rounds" would duplicate P4's
induction, and doc1 shows the stronger form is not inductive — its `F`-cap clause
fails through iteration because finalization lags justification by one round
(rev. 3 §8).

**The bound is abstract.** rev. 3 §8 gives `O(K + c)` rounds measured from
`ref(ρ)`, the first round action time at or after `t_GST` whose opening proposer
is honest, with `c` a small constant covering: one round of timeout-driven
progress across `H`, one round for the height-`(H−1)` card, one honest
opening-proposer round for the first above-`H` confirmation, the justification
round, and one drain round for the graded batch. The statement quantifies the
bound existentially per proposer-recurrence gap rather than naming it, which is
rev. 3's Q6 answered on the time side: the layer states everything against
`ρ.horizon` in `Time`.
-/



namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **The nonfinality-run side condition** (rev. 3 §7.3): no chain state anywhere
in the run records a finalized height above `h_F⁰`.

Two clauses, because "anywhere" has two sources. The first reads the run's own
objects — every block the run contains, and every ancestor of one, since a chain
state is a function of the chain ending at its block (PROTOCOL.md#the-complete-protocol).
Reading the whole run, suffix included, is what lets a condition about
*unrevealed* branches be stated at all (design §5). The second reads the honest
stores directly, which covers a node's own proposal in the case where the horizon
cuts off before relay. -/
def NonfinalityRun (S : Setup V) (ρ : Run V) (h_F0 : Height) : Prop :=
  (∀ B : NamedBlock V, Object.block B ∈ NamedRun.objects ρ →
      ∀ C : NamedBlock V, NamedBlock.Preceq C B →
      (Protocol.derive_named S.E S.cfg C).h_F ≤ h_F0) ∧
    (∀ v ∈ ρ.honest, ∀ t : Time, t ≤ ρ.horizon →
      ∀ B ∈ (ρ.storeAt S v t).T, ((ρ.storeAt S v t).σ B).h_F ≤ h_F0)


/-- **`h_F⁰` is the run's own baseline, not a free cap** (statement reviews).

`NonfinalityRun S ρ h_F0` alone is a one-sided bound, so for any finite run it
holds of every `h_F0` above every finalized height the run contains — including
runs full of fresh finalizations. The premise then open items meaning "sustained
nonfinality above the starting finality". Because `h_F0` is **universally**
quantified in the P5 statements, the failure mode is not a vacuous proof but an
unreachable obligation: the theorem would have to hold for caps the run never
approaches. Pinning `h_F0` to what the honest stores actually hold at the
reference round is what makes the two clauses say the same thing.

Stated at `a_{r_ref}⁻`, the reference round's own anchoring instant. -/
def BaselineAtRef (S : Setup V) (ρ : Run V) (r_ref : Round) (h_F0 : Height) :
    Prop :=
  (∀ v ∈ ρ.honest,
      (ρ.storeBeforeTime S v (S.a r_ref)).core.finalized_height ≤ h_F0) ∧
    ∃ v ∈ ρ.honest,
      (ρ.storeBeforeTime S v (S.a r_ref)).core.finalized_height = h_F0

/-- **The pair recurrence.** Every inclusive round window `[r, r + gap]`
contains TWO CONSECUTIVE proposer-carrier rounds.

This is the recurrence assumption the finality track carries. What it buys
over `MultiProposerRecurrence` is that the SECOND of the two rounds has a carrier
predecessor, and at such a round every honest live confirmation one round
earlier is that round's own opening proposal, so they share a height by
construction — which is exactly the protocol-level premise the recurring
finality exports otherwise have to assume.

It implies `MultiProposerRecurrence` at the same `gap`
(`Proofs.HealingSurface.proposerRecurrence_of_pair`), so every existing
consumer — the seed, the healing route and the moving chain — is unchanged, and
so are all the lag constants, which are computed from `gap` alone. -/
def ProposerPairRecurrence (S : Setup V) (ρ : Run V) (gap : Round) : Prop :=
  ∀ r : Round, ∃ c : Round, r ≤ c ∧ c + 1 ≤ r + gap ∧
    ProposerCarrierAt S ρ c ∧ ProposerCarrierAt S ρ (c + 1)

/-- `ref(ρ)`: the first round whose action time is at or after `t_GST` and whose
opening proposer is honest (rev. 3 §8). The bound below is measured from it. -/
def IsRefRound (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  S.E.t_GST ≤ S.a r ∧ S.E.proposer (S.hc.opening_slot r) ∈ ρ.honest ∧
    ∀ r' : Round, r' < r →
      ¬(S.E.t_GST ≤ S.a r' ∧ S.E.proposer (S.hc.opening_slot r') ∈ ρ.honest)

/-- **P5, healing** (design note P5; rev. 3 §8).

For every admissible nonfinality run with honest committees, honest quorum weight
and the proposer recurrence, there is a round `r` **at or after** `ref(ρ)` and
within the bound of it at which the aligned-round predicate holds — and hence, by
`OptimisticOperation`, the system behaves from `a_r` on as a `t_GST = 0` run does
from round `0`.

`r_ref ≤ r` is the review's repair: without a lower bound on the witness round,
an aligned round from **before** GST satisfies the conclusion and the statement
says nothing about healing. `BaselineAtRef` is the other one; see its own
comment. -/
def HealingReachesAlignedRound (S : Setup V) : Prop :=
  ∀ gap : Round, ∃ bound : Time, 0 ≤ bound ∧
    ∀ (ρ : Run V) (h_F0 : Height) (r_ref : Round),
      Admissible S ρ → HonestCommittees S ρ.honest → BelowOneThird S ρ.honest →
      MultiProposerRecurrence S ρ gap → NonfinalityRun S ρ h_F0 →
      BaselineAtRef S ρ r_ref h_F0 →
      IsRefRound S ρ r_ref → S.a r_ref + bound ≤ ρ.horizon →
      ∃ (r : Round) (Can : Block V) (h_star : Height),
        r_ref ≤ r ∧ S.a r ≤ S.a r_ref + bound ∧
          AlignedRound S ρ r Can h_star (ρ.roundView S r)


/-- **P5 → P4-L, the hand-off** (rev. 3 §7.2; check doc §7 edit 7).

`HealingReachesAlignedRound` concludes `AlignedRound`, while
`FinalityLivenessFromHealing` assumes `AlignedRoundPlus`, `FrontierAligned`, and
the explicit relation `h_c = h* + 1`. Nothing bridged them, so healing composed
with P4 and not with finality liveness — which is the whole point of separating
P4-L. This statement is the bridge, and it claims no more than rev. 3 §7.2's
own last paragraph already argues the two phases deliver:

> the first above-`H` confirmation gives (b); its justification gives (c) and, at
> `H+2` where no honest validator has ever been, (c⁺); the pre-confirmation cap
> gives (d); and the batch graded one round later gives (a).

Read against rev. 4's four clauses (amended per rev. 4 review), with
`h* = H+1` — rev. 4 §13.3's *"`h*` is the frontier the recovery round itself
justifies"*, which is phase (ii)'s above-`H` justification.

* **(d′)** covers `H+1`, the clean healing targets, canonical by Lemma G1, and
  `H+2` upward, which is post-heal. Height `H` contributes nothing: `nj` holds
  there on every branch, so `height_pair` reaches row 7 and every honest
  validator emits a **timeout**, which `targetsAt` does not see. §7.1's one card
  at height `H−1` falls **below** `h*` and is L3's case, not (d′)'s — that is the
  division of labour rev. 4 designed, and reading `h* = H−1` would put the one
  height the adversary holds inside (d′)'s own range.
* **(f)** is `Σ.h_max > H+1`, i.e. the frontier has reached `H+2`. The event
  that discharges it is phase (ii)'s **exit from `H+1`**, not the crossing of
  `H`. `HealingThenFinality`'s companion `FrontierAligned … h_c` with
  `h_c = h* + 1 = H+2` is the same instant, and `H+2` is exactly the "where no
  honest validator has ever been" of the quoted §7.2 paragraph.
* The pre-confirmation cap gives **(d′)** at `h*` as well as above it, because
  it caps the honest state height and no honest validator was gated at `h*` on a
  conflicting branch — this is what makes the honest `H+1` gates uniform.
* **(c⁺)** is unchanged and rides on `AlignedRoundPlus`.

Two of the clauses map onto the frontier bundle rather than onto (a)–(f). (GA) is
the honest opening proposer of the phase-(ii) round — `a_r` is that slot's
confirmation evaluation, so P3(a)(ii) makes every honest `live_confirmed` exactly
the proposed block. (CF) is the load-bearing use of doc2's
`lem:pre-confirmation-cap`: it caps every honest store's state height at `H+1`
before the first recovery confirmation, so no honest validator was ever *gated*
at `H+2` and the records there are genuinely empty. That is the clause (d) cannot
give, and the check doc's edit list says so.

(FC) is deliberately **not** claimed: P5's own hypothesis is a nonfinality run,
so the frontier is entered from a stale `h_F`, and closing the debt is what
`FinalityLivenessFromHealing` does in its two rounds. -/
def HealingThenFinality (S : Setup V) : Prop :=
  ∀ gap : Round, ∃ bound : Time, 0 ≤ bound ∧
    ∀ (ρ : Run V) (h_F0 : Height) (r_ref : Round),
      Admissible S ρ → HonestCommittees S ρ.honest → BelowOneThird S ρ.honest →
      MultiProposerRecurrence S ρ gap → NonfinalityRun S ρ h_F0 →
      BaselineAtRef S ρ r_ref h_F0 →
      IsRefRound S ρ r_ref → S.a r_ref + bound ≤ ρ.horizon →
      ∃ (r : Round) (Can J : Block V) (h_star h_c : Height),
        r_ref ≤ r ∧ S.a r ≤ S.a r_ref + bound ∧
          AlignedRoundPlus S ρ r Can h_star J (ρ.roundView S r) ∧
          FrontierAligned S r (ρ.roundView S r) h_c ∧
          h_c = h_star + 1

end Internal
end DecoupledConsensusModel

end
