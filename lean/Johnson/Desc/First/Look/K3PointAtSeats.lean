-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3PointAtSeats.lean: THE HOST'S OWN SENTENCE (`block_point`,
Johnson/Desc/First/Look/K3Point.lean) AT THE TWO SEATS THAT RUN: the lookup on the calls
(`seatCalls`) and the lookup on the digits (`seatDigits`, Johnson/Desc/First/Look/K3Seat.lean). Two
theorems without a premise on the seat: `SeatReads` is proved of both in
Johnson/Desc/First/Look/K3SeatLaw.lean. So the law stands at the carried record of the proof file's
first chain, not at letters.

Limits: those of K3Point.lean: IT IS A HALF: a sentence on the shape of what the record holds, never
on what was heard. `claim`, the place's numbers and the guests are letters still. No soundness is
claimed.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Point
import Johnson.Desc.First.Look.K3SeatLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Aff Fork)

/-- At the lookup on the calls. -/
theorem block_point_calls {Cl : Type} (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest First.S Cl))
    {s s' : First.S} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}
    (H : (block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s') :
    ∃ g, (seatCalls claim).heard s' = some g ∧
      (∃ h0, Model.Forest.shape p.calls p.lid = .ok h0 ∧
        Model.Forest.pubAsk h0 p.pub = .ok () ∧ g.shape = { h0 with pub := p.pub }) ∧
      g.zx.size = g.shape.dT ∧ g.zy.size = g.shape.rK ∧ g.zk.size = g.shape.NC ∧
      ∀ c, c < g.shape.NC → g.shape.iota.getD c 0 ≤ g.shape.rK ∧
        g.zk.getD c #[] =
          g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx :=
  block_point (seatCalls claim) (seatCalls_reads claim) piece laid before p guests H

/-- At the lookup on the digits. -/
theorem block_point_digits {Cl : Type} (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest First.S Cl))
    {s s' : First.S} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}
    (H : (block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s') :
    ∃ g, (seatDigits claim).heard s' = some g ∧
      (∃ h0, Model.Forest.shape p.calls p.lid = .ok h0 ∧
        Model.Forest.pubAsk h0 p.pub = .ok () ∧ g.shape = { h0 with pub := p.pub }) ∧
      g.zx.size = g.shape.dT ∧ g.zy.size = g.shape.rK ∧ g.zk.size = g.shape.NC ∧
      ∀ c, c < g.shape.NC → g.shape.iota.getD c 0 ≤ g.shape.rK ∧
        g.zk.getD c #[] =
          g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx :=
  block_point (seatDigits claim) (seatDigits_reads claim) piece laid before p guests H

end VerifiableInference.Desc.K3
