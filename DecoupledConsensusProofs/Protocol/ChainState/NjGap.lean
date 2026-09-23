module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.Chain

@[expose] public section

/-!
# Recovery-height state arithmetic

This module contains the chain-local nonjustifiable-height facts. A recovery
height satisfies the protocol's `K` divisibility and `D` debt conditions. The
stored `nj` bit is the entry formula at a finalized height no greater than the
chain state's current `h_F`, so a finalized-height cap makes the recovery height
uniformly nonjustifiable on that chain.

Run-level and quorum lifts belong in the higher `HealingSurface` modules.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace NjGap

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. The arithmetic, stated at `Nat`

`Height` is `abbrev Height:= Nat` (`Substrate/Identifiers.lean:21`), but `omega`
matches the *syntactic* type and does not reduce the abbreviation: every goal
below reports `No usable constraints found` when its variables are typed
`Height`, and closes immediately when they are typed `Nat`. So the five
arithmetic facts phase (i) spends are stated once here over `Nat` and applied at
`Height`, which is definitional. `Proofs.Engine.not_dvd_succ_of_dvd` already follows this
convention. -/

private theorem lt_of_lt_sub {D cap H : Nat} (hD : 1 ≤ D) (h : D < H - cap) :
    cap + 1 < H := by omega


private theorem lt_sub_of_le {D h a b : Nat} (hle : a ≤ b) (h2 : D < h - b) :
    D < h - a := by omega



private theorem ne_succ_of_lt_of_le {a b m : Nat} (h1 : a < m) (h2 : m + 1 ≤ b) :
    ¬(b = a + 1) := by omega


/-! ## 1. `nj` is the entry formula (PROTOCOL.md#the-complete-protocol) -/

section Bookkeeping

variable {σ : ChainState V} {a : CombinedAttestation V}

omit [Fintype V] in

/-- §4 `process_attestation` does not write `nj` (PROTOCOL.md#the-complete-protocol, F4.4).
The eighth field of `Protocol.process_attestation_fields`, which open items at the seven
P1 reads. -/
theorem process_attestation_nj (σ : ChainState V) (a : CombinedAttestation V) :
    (Protocol.process_attestation σ a).nj = σ.nj := by
  unfold Protocol.process_attestation
  split_ifs <;> rfl



end Bookkeeping

section Entry

variable {cfg : HeightConfig}

omit [Fintype V] [DecidableEq V] in
/-- §4 `nj` is antitone in the finalized height (PROTOCOL.md#the-complete-protocol): a chain
that has finalized **less** is at least as nonjustifiable, because the debt
`h − h_F` is at least as large. This is the "one-sided bound" of rev. 3 §7.3, and
it is the only direction phase (i) uses. -/
theorem nonjustifiable_of_le {h h_F cap : Height} (hle : h_F ≤ cap)
    (hnj : Protocol.nonjustifiable cfg h cap = true) :
    Protocol.nonjustifiable cfg h h_F = true := by
  simp only [Protocol.nonjustifiable, Bool.and_eq_true, decide_eq_true_eq] at hnj ⊢
  exact ⟨hnj.1, lt_sub_of_le hle hnj.2⟩

omit [Fintype V] [DecidableEq V] in
/-- §4 the `nj` formula, read forwards (PROTOCOL.md#the-complete-protocol). -/
theorem nonjustifiable_of {h h_F : Height} (hdvd : cfg.K ∣ h) (hdebt : cfg.D < h - h_F) :
    Protocol.nonjustifiable cfg h h_F = true := by
  simp only [Protocol.nonjustifiable, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hdvd, hdebt⟩

/-- **The `nj` invariant** (PROTOCOL.md#the-complete-protocol). A chain state's flag
is the nonjustifiability formula at its own height, evaluated at *some* finalized
height no larger than the one it now records.

The inequality is what makes this an invariant. `advance_height` writes the flag
from the `h_F` of the moment it enters the height, and the flag is then "fixed
until the height changes" (PROTOCOL.md#the-complete-protocol) while `h_F` can still advance
underneath it — `process_height_events`' finality branch falls through and both
height branches may decline to fire. So equality is false and `≤` is true, in the
direction that keeps the flag *set*. -/
def NjEntry (cfg : HeightConfig) (σ : ChainState V) : Prop :=
  ∃ h_F' : Height, h_F' ≤ σ.h_F ∧ σ.nj = Protocol.nonjustifiable cfg σ.h h_F'

omit [Fintype V] [DecidableEq V] in
/-- §4 the initial state satisfies it (PROTOCOL.md#the-complete-protocol, F4.7): `h = 1`,
`h_F = 0` and `K ≥ 2`, so the literal `false` the document writes **is** the
formula. -/
theorem njEntry_initial (cfg : HeightConfig) :
    NjEntry cfg (ChainState.initial : ChainState V) := by
  refine ⟨0, Nat.le_refl 0, ?_⟩
  have hK : ¬ cfg.K ∣ 1 := by
    intro h
    have h1 := Nat.le_of_dvd Nat.one_pos h
    have h2 := cfg.K_ge_two
    omega
  simp [Protocol.nonjustifiable, ChainState.initial, hK]

variable (E : Env V)

/-- §4 the finality branch never lowers `h_F` (PROTOCOL.md#the-complete-protocol): it fires
only under `h_F < h_j` and writes `h_F ← h_j`. -/
theorem le_afterFin_h_F (σ : ChainState V) : σ.h_F ≤ (Protocol.afterFin E σ).h_F := by
  rw [Protocol.afterFin_h_F]
  split_ifs with h
  · exact Nat.le_of_lt (Protocol.lt_of_finalityReady E h)
  · exact Nat.le_refl _


end Entry

/-! ## 2. Uniform `nj` at a recovery height (rev. 3 §7.3) -/

section Uniform

variable (E : Env V) (cfg : HeightConfig)

/-- **A recovery height** (rev. 3 §7.1): periodic, and past the debt bound
measured from the run's baseline. Both conjuncts are `nonjustifiable`'s own two
tests with `h_F⁰` in place of a branch's `h_F` (PROTOCOL.md#the-complete-protocol). -/
def RecoveryHeight (cfg : HeightConfig) (h_F0 H : Height) : Prop :=
  cfg.K ∣ H ∧ cfg.D < H - h_F0


omit [Fintype V] [DecidableEq V] in
/-- A recovery height is at least two above the baseline: `D ≥ 1`
(PROTOCOL.md#the-complete-protocol). Small, and keeps `H − 1` honest under truncated
subtraction. -/
theorem lt_of_recoveryHeight {cfg : HeightConfig} {h_F0 H : Height}
    (h : RecoveryHeight cfg h_F0 H) : h_F0 + 1 < H :=
  lt_of_lt_sub cfg.D_ge_one h.2


end Uniform

/-! ## 3. No justification at the recovery height (rev. 3 §7.1) -/

section NoJustification

variable (E : Env V) (cfg : HeightConfig)

/-- §4 the `nj` flag closes the justification guard (PROTOCOL.md#the-complete-protocol,
1166–1171). The one place `nj` is read, and the whole of `Healing/Nonjustifiable`'s
first fact in the form phase (i) consumes. -/
theorem targetReady_eq_false_of_nj {σ : ChainState V} (h : σ.nj = true) :
    Protocol.targetReady E σ = false := by
  simp [Protocol.targetReady, h]




end NoJustification


/-! ## 4. Pure unselectability arithmetic -/

section Unselectable

omit [Fintype V] in
/-- **The `nj` gap closes the cascade gate** (rev. 3 §7.1;
PROTOCOL.md#the-complete-protocol). `get_fg_root` returns `Σ.J` only at
`Σ.h_max = Σ.h_j + 1`; with the justification below `H` and the frontier at or
above `H + 1` the two differ by at least one, so the walk anchors at `Σ.F`.

This is L3 (`AlignedRoundLemmas.sub_frontier_reveal_harmless`) with the recovery
height in place of the frontier `h*` — and it is the same one-line arithmetic,
which is the point rev. 3 §7.1 makes: "`nj` forces a two-height separation
between the highest certificate and the frontier, and the gate is exactly a test
that the separation is one". -/
theorem get_fg_root_eq_F_of_gap {st : Protocol.Store V} {H : Height}
    (hj : st.h_j < H) (hmax : H + 1 ≤ st.h_max) :
    Protocol.get_fg_root st.toHealing.toFG = st.F := by
  have hne : ¬(st.h_max = st.h_j + 1) := ne_succ_of_lt_of_le hj hmax
  simp [Protocol.get_fg_root, Protocol.Store.toHealing, hne]



end Unselectable


end NjGap
end Proofs
end DecoupledConsensusModel

end
