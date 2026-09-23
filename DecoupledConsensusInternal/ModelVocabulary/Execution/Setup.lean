module
public import DecoupledConsensusModel

@[expose] public section

/-!
# Execution layer — the fixed data of a run
(§2, §3.1; PROTOCOL.md#the-complete-protocol)

`Setup` bundles what every handler already takes — the environment, the two
parameter structures, and the per-validator node identity — so that no statement
below has to thread five arguments.

`PublicTime` is the tick schedule. The four per-slot instants of
PROTOCOL.md#the-complete-protocol are `t_s + kΔ` for `k ∈ {0,1,2,3}` and `t_s = 4Δs`, so the
public times are exactly the natural multiples of `Δ`. Stating the schedule this
way is what makes the view freeze `t_s + 3Δ` a tick time even though no `on_tick`
branch fires there — the plan's flag F-a, and what row C1's stamping rule needs
(design §3, §9).

This library states; it never proves (`conventions.md:4`,
`the design note:29–30`). The agreement between `PublicTime` and the four instants
is `Proofs/Execution.lean`'s `publicTime_iff`.
-/

namespace DecoupledConsensusModel
namespace Execution

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

namespace Setup

variable (S : Setup V)

end Setup


/-- A public time: an instant at which every honest node ticks
(PROTOCOL.md#the-complete-protocol).

`t_s = 4Δs` and the per-slot instants are `t_s + kΔ` for `k ∈ {0,1,2,3}`, so the
public times are the natural multiples of `Δ` — which is also `a_r = Δ(4rR + 6)`
and the grade cutoffs `Γ_r^{0,1,2}`. `Γ_r^{−1} = t_{rR} − Δ` is a multiple of `Δ`
only for `r ≥ 1`: at `r = 0` it is `−Δ`, which is not `kΔ` for a natural `k`. No
statement compares a tick time to `Γ^{−1}`, so nothing rests on it. Flag F-a: the
view freeze `t_s + 3Δ` is a
tick time under this reading, which is what open items an object delivered in
`(t_s+3Δ, t_s+4Δ)` from carrying the stamp `t_s+2Δ` and so passing a freeze
cutoff it should miss (design §3, §9). -/
def PublicTime (S : Setup V) (t : Time) : Prop :=
  ∃ k : Nat, t = (k : Time) * S.E.Δ

/-- The timeout delay in healing rounds. The default is the established
two-round bound; `extraRounds = 1` selects three rounds. This is a named
hypothesis rather than a `Setup` field, so transition fixtures can use other
delays. Timing proofs state separately which lower or upper bound they use. -/
def TimeoutDelayBound (S : Setup V) (extraRounds : Nat := 0) : Prop :=
  S.cfg.timeoutDelay = (2 + extraRounds) * S.hc.R

namespace Setup

def extraRounds (S : Setup V) : Nat := S.cfg.timeoutDelay / S.hc.R - 2

theorem timeoutDelayBound (S : Setup V) : TimeoutDelayBound S S.extraRounds := by
  unfold TimeoutDelayBound extraRounds
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 3) S.hc.R_ge_three
  have hquot : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).2 S.timeout_rounds.2
  have hdiv : S.cfg.timeoutDelay =
      (S.cfg.timeoutDelay / S.hc.R) * S.hc.R :=
    (Nat.div_mul_cancel S.timeout_rounds.1).symm
  have hsum : 2 + (S.cfg.timeoutDelay / S.hc.R - 2) =
      S.cfg.timeoutDelay / S.hc.R := by
    omega
  calc
    S.cfg.timeoutDelay = (S.cfg.timeoutDelay / S.hc.R) * S.hc.R := hdiv
    _ = (2 + (S.cfg.timeoutDelay / S.hc.R - 2)) * S.hc.R := by rw [hsum]

end Setup

end Execution
end DecoupledConsensusModel

end
