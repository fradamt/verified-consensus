module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.Confirmation
public import DecoupledConsensusInternal.Definitions.NamedEvidence
public import DecoupledConsensusInternal.Internal.HeightProgress
public import DecoupledConsensusInternal.AlignedRound

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Raw honest height frontiers -/

/-! ## The exact proposal block -/

/-- The Rule A consumption gate at one proposal: the named parent of the
slot's honest proposal carries a height transition old enough for the
timeout rows to be consumable at `s`. A premise, so it quantifies the
proposal witness and the parent (no proposal, no obligation); the
parent's state is the named derivation, never the erased one. -/
def ProposalTimeoutMatureAt
    (S : Setup V) (rho : Run V) (s : Slot) : Prop :=
  ∀ B : NamedBlock V, Statements.Instantiation.proposedBlockAt S rho s = some B →
    ∀ p : NamedBlock V, NamedBlock.parent? B = some p →
      (Protocol.derive_named S.E S.cfg p).T_h.slot + S.cfg.timeoutDelay ≤ s

/-- **Open (Rule A residual).** Every opening proposal in the stated
round interval satisfies the timeout-row consumption gate. -/
def OpeningProposalTimeoutMatureOn
    (S : Setup V) (rho : Run V) (lo hi : Round) : Prop :=
  ∀ q, lo ≤ q → q ≤ hi →
    ProposalTimeoutMatureAt S rho (S.hc.opening_slot q)

/-! ## The three conclusions, shared by P3(a), P3(b) and P4's (C1) -/

/-! ### Genuine-confirmation renewal

The original `ProposalConfirmedFrom` below identifies confirmation liveness
with exact confirmation of the block emitted by the same slot's honest
proposer. The integrated Section 7 protocol makes a different promise:
`update_confirmation` confirms the ordinary composed walk when that walk clears
the Goldfish gate, and otherwise records only the FG-root floor marker.

The definitions in this section expose that exact distinction without adding a
second selector. They are the local values of Section 7's existing
`update_confirmation` body, evaluated in the store handed to the confirmation
duty. -/

/-! ## P3(a) — the available chain at `t_GST = 0` -/

/-- **Open (Rule B residual).** Every honest finality target has an
honest height-target source strictly before the finality emission. Rule B no
longer derives this from the anti-slashing record because the target entry can
be empty when the finality pair is created. -/
def FinalityTargetHeightSource (S : Setup V) (ρ : Run V) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time),
    a.val_index ∈ ρ.honest →
      ρ.emits S a.val_index (Object.attest a) ta →
        ∀ h target, a.finality_pair = some ⟨h, target⟩ →
          ∃ (b : NamedAttestation V) (tb : Time),
            b.val_index ∈ ρ.honest ∧
              ρ.emits S b.val_index (Object.attest b) tb ∧
                tb < ta ∧ b.height_pair = NamedHeightPair.vote h target false

/-- **P3(a)** (design note P3(a); rev. 3 §8). For every admissible run with
`t_GST = 0`, honest committees, a global honest-weight majority, and the
source-exact Rule B residual, the available chain holds from time `0`.

Unconditional in the run: no aligned round, no good state, no fault bound beyond
the two counting assumptions.

**Not a corollary of P4, and the gap is one interval.** rev. 3 §6 verifies
`AlignedRound(0)` of the initial world with `Can = genesis`, `h* = 0`,
`J = genesis` — genesis is justified at height 0 by definition
(PROTOCOL.md#the-complete-protocol) — so `OptimisticOperation`'s (C1) applies at `r₀ = 0`.
But (C1) is `AvailableChainFrom S ρ (S.a 0)` and `S.a 0 = slotStart Δ 0 + 6Δ`,
while this statement starts at `0`; the predicate is antitone in its left
endpoint, so the instantiation runs the wrong way. The difference is real, not
cosmetic: `ProposalConfirmedFrom S ρ 0` covers slot 1, whose proposal time is
`4Δ`, and `ConfirmationCompatibleFrom` loses the whole interval `[0, 6Δ)`.

The residue is small — nothing is confirmed before `6Δ`, because the first
`update_confirmation` fires at slot 1's support cutoff — but it is a lemma about
the initial store, not a corollary of P4, and P3(a) is stated separately so that
the obligation is visible. -/
def AvailabilityGSTZero (S : Setup V) : Prop :=
  ∀ ρ : Run V, Admissible S ρ → S.E.t_GST = 0 →
    HonestCommittees S ρ.honest → HonestWeightMajority S ρ.honest →
    FinalityTargetHeightSource S ρ →
    HonestHeadExtendsStableFrom S ρ 0 →
    AvailableChainFrom S ρ 0


/-- The source-exact GST-zero confirmation statement. It asks for genuine
confirmation renewal, not exact capture of the same-slot proposal.

TEMPORARY premise (addendum 34, option (a)):
`HonestHeadExtendsStableFrom` says the confirmation duty's stable write
precedes the record it writes at the same read. It is discharged, and removed,
by the stable-record canonicity theorem; that discharge is mandatory. -/
def AvailabilityGSTZeroRenewal (S : Setup V) : Prop :=
  ∀ ρ : Run V, Admissible S ρ → S.E.t_GST = 0 →
    HonestCommittees S ρ.honest → HonestWeightMajority S ρ.honest →
    FinalityTargetHeightSource S ρ →
    HonestHeadExtendsStableFrom S ρ 0 →
    AvailableConfirmationsFrom S ρ 0

/-! ## P3(b) — the available chain from an aligned round -/

/-- **P3(b)** (design note P3(b); rev. 3 §8). The same conclusions for all times
and slots at or after `a_{r₀}`, under `AlignedRound(r₀)` with `a_{r₀} ≥ t_GST`;
and every confirmed block from `a_{r₀}` on lies on a single chain extending
`Can`.

Reading note on the last clause: "one chain extending `Can`" is stated as
compatibility with `Can`, not as `Can ⪯`. A node whose own `live_confirmed` was
strictly below `Can` at `a_{r₀}⁻` catches up within a slot rather than instantly,
so `Can ⪯` is false at the boundary while compatibility — which is the safety
content — holds throughout. -/
def AvailabilityFromAlignedRound (S : Setup V) : Prop :=
  ∀ (ρ : Run V) (r₀ : Round) (Can : Block V) (h_star : Height),
    Admissible S ρ → HonestCommittees S ρ.honest → BelowOneThird S ρ.honest →
    S.E.t_GST ≤ S.a r₀ →
    AlignedRound S ρ r₀ Can h_star (ρ.roundView S r₀) →
    AvailableChainFrom S ρ (S.a r₀) ∧
      ∀ v ∈ ρ.honest, ∀ t : Time, S.a r₀ ≤ t → t ≤ ρ.horizon →
        Block.compatible Can (ρ.storeAt S v t).latest_confirmed = true

end Internal
end DecoupledConsensusModel

end
