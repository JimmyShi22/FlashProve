-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Johnson/Layers/Ride.lean: the short sumcheck (Cb/G6/Johnson/Layers/Short.lean) whose target is
sent in round 0.

Definitions, one statement and its proof. The routines of the Lean model of the C++ verifier admit
that the target of a sumcheck is part of round 0's message: the value sent for the hidden sum and
the sum of the hiding polynomial go out together, both before ε is drawn (OnBytes/Model/Hide.lean:
`SubM.claimsIn`, `SubM.readSum`; OnBytes/Model/Psc.lean: `pscBeginAt`). Which sub-proof does so is
not said in these files. The library's block has the target in the statement.

Main names:
  `rRound0`, `shapeR Y`: the rounds of the short sumcheck with two scalars in round 0: the target,
    then the sum of the hiding polynomial.
  `rTarget`, `unride`: the target that a transcript sent; the transcript without it.
  `ride_doomed`: for each fixed tuple of entries m and each state, with no premise on a claim: the
    prover is lost (`Doomed`, Iop/Rbr.lean), with the library's numbers, towards: if the sum claim
    at the target that it sent is false of m, then whatever the library's verifier puts out on the
    completed transcript is false of m. In words: whichever target the prover sends, either it is
    the true one or the prover has lost.

Premises: `Y.VarsOK`, `Y.DegOK`, `Y.ValInj` (the library's).
Limits: the file does not say that more than one scalar may ride, nor anything on the programs'
routine. Nothing on zero knowledge; "hidden" and "hiding" are names.

-/
import Iop.Compose
import Cb.G6.Johnson.Layers.Short

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.L5.Layers
open Iop Prob Cb

variable {E : Type} [Field E] [Fintype E] (Y : PscPar E)

/-- Round 0 with the target riding: two scalars, then ε from all of E. -/
@[reducible] def rRound0 (E : Type) [Field E] [Fintype E] : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := E × E,
    Chal := E, dOrc := (), dPlain := (0, 0) }

/-- The rounds of the short sumcheck whose target is sent. -/
abbrev shapeR : Shape := rRound0 E :: (sRounds Y.fmt ++ [pRoundV E Y.A])

/-- The errors behind round 0. -/
def errS : Err (sRounds Y.fmt ++ [pRoundV E Y.A]) :=
  errTo _ (pRounds Y.fmt ++ [pRoundV E Y.A]) (Err.app (pErr Y.fmt) ((0, ()) : Err [pRoundV E Y.A]))

/-- The target that was sent. -/
def rTarget (t : Tr (shapeR Y)) : E := t.1.2.1
/-- The transcript without the target. -/
def unride (t : Tr (shapeR Y)) : Tr (shapeS Y) := (((), t.1.2.2), t.2.1, t.2.2)

/-- Whichever target the prover sends, either it is the true one or the prover has lost. -/
theorem ride_doomed (Ex : ExtSpec) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (st : Y.St)
    (F : HFixs (Y.vars st)) (y : Ex.Str) (m : Y.J → E) :
    Doomed (shapeR Y) (1, errS Y) fun t =>
      ¬ Y.SumHolds (rTarget Y t, st) m →
        ∀ o, (Y.psc Ex).out (rTarget Y t, st) y
            ((carryS Y (rTarget Y t, st) F Ex).tr (unride Y t)) = some o → ¬ Y.OutHolds o m :=
  fun msg => by
    by_cases h : Y.SumHolds (msg.2.1, st) m
    · rw [cnt_false fun c hc => hc (Doomed.of_forall _ _ fun t hn => absurd h hn)]
      exact Nat.zero_le _
    · exact le_trans (cnt_mono fun c hc hd => hc (Doomed.mono _ _ (fun t ht _ => ht) hd))
        (short_doomed Y Ex hV hD hI (msg.2.1, st) F y m h ((), msg.2.2))

end Johnson.L5.Layers
