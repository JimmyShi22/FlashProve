-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/KitHon.lean: honest provers of composed protocols with slots: helper lemmas.

Helper definitions and lemmas on the honest prover, the verifier's randomness, and the order of
shared and local rounds.
In a protocol with slots (`BatchInteractiveOracleProof`) the honest prover consists of a strategy for the shared
component, which sees the shared challenges only, and one for each slot (`SStrat`, `LStrat`,
Iop/Batch.lean; `SStrat.zip` combines the two into a strategy on a slot's transcripts). Here they
are built for rounds s ++ t where only the slots send in s (`SStrat.skip`, `LStrat.bind`); the
combined strategy is the sequential composition `Strat.bind` (`zip_skip_bind`).

Notation: from Iop/Batch.lean: `Kind`: a round is called shared (sh) or local (lo) after its
verifier message; `RAnn.ofSlot k r`: a round in which only the slots send: there is no shared prover
message;
`RoundSplits.summary s A`: of each round: its kind; that it has no shared prover message
(`Subsingleton a.M0`); that the slots send no message (`Subsingleton a.Mj`).
-/
import Iop.Batch
import Iop.ShapeKit

set_option autoImplicit false

namespace Iop

/-! ## 1. The honest prover -/

/-- The shared strategy sends nothing in s, where only the slots send. -/
def SStrat.skip (k : Kind) :
    (s : Shape) → {t : Shape} → {A' : RoundSplits t} → SStrat t A' →
    SStrat (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot k) s) A')
  | [], _, _, σ => σ
  | _ :: s, _, _, σ => ((), fun _ => SStrat.skip k s σ)

/-- The slot sends σ's messages in s, where only the slots send, and goes on with the result. -/
def LStrat.bind (k : Kind) :
    {s t : Shape} → {A' : RoundSplits t} → {β : Type} → Strat s β → (β → LStrat t A') →
    LStrat (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot k) s) A')
  | [], _, _, _, b, g => g b
  | _ :: _, _, _, _, (m, κ), g => (m, fun c => LStrat.bind k (κ c) g)

theorem zip_skip_bind (k : Kind) :
    ∀ {s t : Shape} {A' : RoundSplits t} {β : Type} (σ0 : SStrat t A')
        (σ : Strat s β) (g : β → LStrat t A'),
      (SStrat.skip k s σ0).zip (LStrat.bind k σ g) = Strat.bind σ fun b => σ0.zip (g b)
  | [], _, _, _, _, _, _ => rfl
  | r :: s, t, _, _, σ0, (m, κ), g => by
      show ((m, fun c =>
            (SStrat.skip k s σ0).zip
              (LStrat.bind k (κ c) g)) : r.Msg × (r.Chal → Strat (s ++ t) Unit)) =
        (m, fun c => Strat.bind (κ c) fun b => σ0.zip (g b))
      exact congrArg (Prod.mk m) (funext fun c => zip_skip_bind k σ0 (κ c) g)

/-- The shared strategy sends nothing to the end. -/
def SStrat.silent (k : Kind) : (s : Shape) → SStrat s (RoundSplits.const (RAnn.ofSlot k) s)
  | [] => ()
  | _ :: s => ((), fun _ => SStrat.silent k s)

/-- The slot sends σ's messages to the end. -/
def LStrat.last (k : Kind) : {s : Shape} → Strat s Unit → LStrat s (RoundSplits.const (RAnn.ofSlot k) s)
  | [], _ => ()
  | _ :: _, (m, κ) => (m, fun c => LStrat.last k (κ c))

theorem zip_silent_last (k : Kind) :
    ∀ {s : Shape} (σ : Strat s Unit), (SStrat.silent k s).zip (LStrat.last k σ) = σ
  | [], _ => rfl
  | r :: s, (m, κ) => by
      show ((m, fun c =>
            (SStrat.silent k s).zip (LStrat.last k (κ c))) : r.Msg × (r.Chal → Strat s Unit)) =
        (m, κ)
      exact congrArg (Prod.mk m) (funext fun c => zip_silent_last k (κ c))

/-! ## 2. The verifier's randomness -/

/-- The challenges of a first part s of local rounds, among the local challenges of a slot. -/
def RhoLo.front :
    (s : Shape) → {t : Shape} → {A' : RoundSplits t} →
    RhoLo (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') → Rho s
  | [], _, _, _ => ()
  | _ :: s, _, _, (c, l) => (c, RhoLo.front s l)

theorem RhoLo.front_lo : ∀ (s : Shape) {t : Shape} (A' : RoundSplits t) (ρ : Rho (s ++ t)),
    RhoLo.front s (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') ρ) = Rho.fst ρ
  | [], _, _, _ => rfl
  | r :: s, _, A', (c, ρ) => by
      show ((c, RhoLo.front s
            (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') ρ)) : r.Chal × Rho s) =
        (c, Rho.fst ρ)
      rw [RhoLo.front_lo s A' ρ]

/-- The shared challenges of s ++ t determine those of the second part t. -/
theorem Rho.sh_snd_eq :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) {ρ ρ' : Rho (s ++ t)}, Rho.sh (RoundSplits.app A B) ρ =
        Rho.sh (RoundSplits.app A B) ρ' →
      Rho.sh B (Rho.snd (s := s) ρ) = Rho.sh B (Rho.snd (s := s) ρ')
  | [], _, _, _, _, _, h => h
  | _ :: s, _, (_, A), B, (_, _), (_, _), h => Rho.sh_snd_eq (s := s) A B (congrArg Prod.snd h)

/-! ## 3. The order of shared and local rounds

`RoundSplits.summary s A` (Iop/Batch.lean) lists, of each round: its kind; that it has no shared prover
message (`Subsingleton a.M0`); that the slots send no message (`Subsingleton a.Mj`).
`RoundSplits.summary_app`: the summary of `RoundSplits.app A B` is that of A followed by that of B.
`RoundSplits.mem_summary_const`: every entry of the summary of `RoundSplits.const f s` is that of `f r` for some
round r. `RoundSplits.summary_ne_nil`: for s ≠ [] the summary is not empty. -/

theorem RoundSplits.summary_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t),
      RoundSplits.summary (s ++ t) (RoundSplits.app A B) = RoundSplits.summary s A ++ RoundSplits.summary t B
  | [], _, _, _ => rfl
  | _ :: _, _, (a, A), B =>
    congrArg (List.cons (a.kind, Subsingleton a.M0, Subsingleton a.Mj)) (RoundSplits.summary_app A B)

theorem RoundSplits.mem_summary_const {f : ∀ r : Round, RAnn r} :
    ∀ {s : Shape} {x : Kind × Prop × Prop}, x ∈ RoundSplits.summary s (RoundSplits.const f s) →
      ∃ r, x = ((f r).kind, Subsingleton (f r).M0, Subsingleton (f r).Mj)
  | [], _, h => absurd h (List.not_mem_nil)
  | r :: _, _, h => by
      rcases List.mem_cons.mp h with h | h
      · exact ⟨r, h⟩
      · exact RoundSplits.mem_summary_const h

theorem RoundSplits.summary_ne_nil : ∀ {s : Shape} (A : RoundSplits s), s ≠ [] → RoundSplits.summary s A ≠ []
  | [], _, h => absurd rfl h
  | _ :: _, (_, _), _ => List.cons_ne_nil _ _

end Iop
