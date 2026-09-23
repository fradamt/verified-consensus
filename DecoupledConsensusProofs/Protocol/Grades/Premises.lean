module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedStableChainOutage
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival

@[expose] public section

/-! Stage-1 premise of the asynchrony-resilience second half.
`HonestConfirmedAbove` combines `HonestConfirmedAtOrAbove` and
`HonestHeadHeldAbove` at the same round `s`. It is the public premise of the
second-half result.

`HonestConfirmedAtOrAbove` and `HonestHeadHeldAbove` are individually usable
building blocks, not premises on their own: neither appears alone in the
signature of `common_support_base`, only as the two components of `hconf`.
`HealthySGArrival` is a third intermediate predicate. -/

/-! ## The `Δ` grid

`OutageExecution.boundaryPublic` puts the outage boundary on the `Δ` grid.
Action times `Δ(4qR + 6)` and the phase cutoffs are on the same grid, so a
strict inequality between two grid times leaves a full delay of room. The
toolchain note applies: `omega` refuses a goal stated at the `Time` alias and
cannot see `Δ_pos`, so the arithmetic core is a private helper over bare `Int`
and `linarith` is not importable in this cone. -/


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]



/-- A time that is an INTEGER multiple of `Δ`. `Execution.PublicTime` is
the natural-multiple case; the phase cutoffs sit below the opening and need the
integer form. -/
def OnDeltaGrid (S : Setup V) (t : Time) : Prop := ∃ k : Int, t = S.E.Δ * k

/-- Arithmetic core over bare `Int`. -/
private theorem grid_gap : ∀ d x y : Int, 0 < d → d * x < d * y → d * x + d ≤ d * y := by
  intro d x y hd h
  have hxy : x < y := by
    by_contra hcon
    exact absurd (Int.mul_le_mul_of_nonneg_left (Int.not_lt.mp hcon) hd.le) (not_le.mpr h)
  have h1 : x + 1 ≤ y := by omega
  calc d * x + d = d * (x + 1) := by ring
    _ ≤ d * y := Int.mul_le_mul_of_nonneg_left h1 hd.le

theorem onDeltaGrid_of_public (S : Setup V) (t : Time)
    (h : Execution.PublicTime S t) : OnDeltaGrid S t := by
  obtain ⟨k, hk⟩ := h
  exact ⟨(k : Int), by rw [hk]; ring⟩

theorem onDeltaGrid_min (S : Setup V) {x y : Time}
    (hx : OnDeltaGrid S x) (hy : OnDeltaGrid S y) : OnDeltaGrid S (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; exact hx
  · rw [min_eq_right h]; exact hy

/-- `S.a q = Δ(4 · sR + 6)` where `s` is the opening slot. -/
theorem onDeltaGrid_a (S : Setup V) (q : Round) : OnDeltaGrid S (S.a q) :=
  ⟨4 * ((S.hc.opening_slot q : Nat) : Time) + 6, by
    simp only [Setup.a, Protocol.HealConfig.a, slotStart]
    ring⟩

/-- `Γ_r^2 = Δ(4 · sR − 5)` where `s` is the opening slot. -/
theorem onDeltaGrid_early_g2 (S : Setup V) (r : Round) :
    OnDeltaGrid S (early S.E S.hc r .g2) :=
  ⟨4 * ((S.hc.opening_slot r : Nat) : Time) - 5, by
    simp only [early, opening, Phase.earlyOffset, Protocol.proposal_time, Env.t, slotStart]
    ring⟩

/-- A grid time strictly past an action time is a full delay past it. -/
theorem a_add_delta_le_of_lt_grid (S : Setup V) (t : Time) (hgrid : OnDeltaGrid S t)
    (q : Round) (h : S.a q < t) : S.a q + S.E.Δ ≤ t := by
  obtain ⟨k, hk⟩ := hgrid
  obtain ⟨m, hm⟩ := onDeltaGrid_a S q
  rw [hk, hm] at h ⊢
  exact grid_gap S.E.Δ m k S.E.Δ_pos h

/-- The form the boundary uses, from `OutageExecution.boundaryPublic`. -/
theorem a_add_delta_le_of_lt_public (S : Setup V) (b0 : Time)
    (hpub : Execution.PublicTime S b0) (q : Round) (h : S.a q < b0) :
    S.a q + S.E.Δ ≤ b0 :=
  a_add_delta_le_of_lt_grid S b0 (onDeltaGrid_of_public S b0 hpub) q h

#print axioms a_add_delta_le_of_lt_public


/-- The same statement as the selection's `HonestConfirmedAbove`, with the
round bound relaxed from `s < a.round` to `s ≤ a.round`. This, and not the
strict form, is the shape  needs: the boundary round `ρ` satisfies only
`s + 1 ≤ ρ`, so the last round whose rows are certainly retained at `b0` is
`ρ - 1`, which is the stable round `s` itself whenever `ρ = s + 1` — the
typical case, since `FormationMargin S s b0` places `b0` just after round
`s + 1`'s opening. -/
def HonestConfirmedAtOrAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (.attest a) t → t < b0 → s ≤ a.round →
    ∀ key, a.confirmed = some key →
      ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
        Block.Preceq P K.erase


/-- Companion of `HonestConfirmedAtOrAbove` on the *reader* side.
`OutageEntryRevision.covers` and `DecoupledConsensusModel.Protocol.bodyReady` both look the
confirmed root up in the reader's own tree, so knowing that the head exists in
the run and lies above the stable chain is not enough: the reader must hold it.
This premise says every honest pre-outage confirmed head, from a round at or
above the stable round, is held at every honest reader from one delay after the
sender's action onwards, is compatible with that reader's finalized prefix, and
carries a block stamp no later than one delay after the action.

Addendum 34 17. Three changes from the previous text: the
emission margin is `t + Δ ≤ b0` rather than `t < b0`, the read is at `t + Δ` or
later rather than at `t` or later, and the clause is guarded by `F(cut) ⪯ P`.
The guard is what makes the clause true: compatibility of an ARBITRARY honest
confirmed head with the reader's finalized block does not follow from the outage
premises. The consumers only ever need the clause at a reader whose finalized
block has not passed `P`, which is exactly `NeedsSG`, and that yields the
guard. -/
def HonestHeadHeldAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (.attest a) t → t + S.E.Δ ≤ b0 → s ≤ a.round →
    ∀ reader ∈ rho.honest, ∀ cut : Time, t + S.E.Δ ≤ cut →
      Block.Preceq (NamedRun.stateBeforeTime S rho cut reader).st.core.F P →
      ∀ key, a.confirmed = some key →
        ∃ H : NamedBlock V,
          H ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies ∧ H.root = key ∧
          Block.compatible H.erase
            (NamedRun.stateBeforeTime S rho cut reader).st.core.F = true ∧
          ∀ gamma : Time, t + S.E.Δ ≤ gamma →
            stampedBefore (NamedRun.stateBeforeTime S rho cut reader).st.core.timestamp_block
              gamma H.erase = true


/-- Additive correction of `ConfirmationCoverageBefore`.

The current outage consumer uses only the anchor coverage before `b0`; its
active-G2 outputs are rebuilt from the post-boundary round invariant. The
same-round active-G2 field is therefore not part of this proof-layer clause. -/
def ConfirmationCoverageBefore' (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (s : Round) (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ t : Time,
    S.a s ≤ t → t < b0 →
    0 < S.E.slotOf t → t = Protocol.support_cutoff S.E (S.E.slotOf t) →
    Block.Preceq P (sgRoot S (confirmationReadAt S rho w t))

/-- Stage-1 premise, clause 4 (addendum 34 rulings 15 and 17, and
1708): at every honest reader, every round after the stable round that acted
before the outage either had already finalized past the stable chain or froze a
G2 root covering it. Discharged in stage 2.

This is the `RoundInvariant.sg` shape, so the pre-outage segment and the ladder
present the same disjunction to their consumers. The G1 conjunct is dropped: no
site projects it, and the interpolation route to the anchor derives the G1 slot
from the G2 slot instead. -/
def PreBoundaryFrames (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ q : Round, s + 1 ≤ q → S.a q < b0 →
    let n := NamedRun.readAt S rho (domain S.E S.hc q .g1) w
    Block.Preceq P n.st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing q).g2 = some (some raw) ∧
          Block.Preceq P raw


/-- Additive three-clause fold consumed by the outage chain. The corrected
confirmation-coverage clause remains an audit leaf, but no downstream proof
projects it: the chain uses clauses 1, 2, and 5. The frozen public
definitions are unchanged. -/
def HonestConfirmedAbove' (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  HonestConfirmedAtOrAbove S rho b0 s P ∧ (HonestHeadHeldAbove S rho b0 s P ∧
    PreBoundaryFrames S rho b0 s P)



/-- Intermediate predicate, not a premise.
`Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2` restated at the deadline its
own proof uses. The available lemma asks for `FormationMargin S a.round b0`; the
only consequence of that hypothesis it consumes is
`formation_margin_action_deadline`, i.e. `S.a a.round + Δ ≤ b0`.  has
the deadline for round `ρ - 1` but not the margin, so this premise stands in
for the production restatement. Nothing else changes. -/
def HealthySGArrival (S : Setup V) (rho : NamedRun V) (b0 : Time) : Prop :=
  ∀ a : NamedAttestation V, a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) →
    S.a a.round + S.E.Δ ≤ b0 →
    ∀ reader ∈ rho.honest,
      let n := NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (a.round + 1) DecoupledConsensusModel.Protocol.Phase.g2) reader
      a ∈ n.st.sg_rows a.round ∧
      occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
        (DecoupledConsensusModel.Protocol.early S.E S.hc (a.round + 1) DecoupledConsensusModel.Protocol.Phase.g2) = true

/-- `HealthySGArrival` discharged from an outage execution, via the production
restatement `Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2_of_deadline`. -/
theorem healthySGArrival_of_exec (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : Internal.NamedOutageEntry.OutageExecution S rho b0 b1) :
    HealthySGArrival S rho b0 := by
  intro a ha hem hdead reader hreader
  obtain ⟨hheld, hoccur, _⟩ :=
    Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2_of_deadline S rho b0 b1 hexec ha hem hdead
      reader hreader
  exact ⟨hheld, hoccur⟩

#print axioms healthySGArrival_of_exec

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
