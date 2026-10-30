-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K12.Law.PubOk
import Fmt.Rules6Draws
/-
Johnson/Desc/K12/Law/BatOneOk.lean: ONE TEST WITH CODE ON THE PLAN: the place's first written round,
"BAT", draws one element of the extension field and nothing else, and its logN is at most 64.
DEFINITIONS WITH CODE ALONE, NO THEOREM,
NO Mathlib: so that it can be compiled and run. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  batOneOn w · batOneOk p   Fmt.dsOf w.entry w.kind == [.elem, .trits 0] && logN ≤ 64, at the first of writtenOf p.nums; false where there is none
  batFreeOn w · batFreeOk p   … && work == 0: the round asks no bits of work
  batOneLines               the lines that a run prints, with three controls, each due false: one drawn element more · one position drawn · one bit of work asked
WHAT FOR: the two premises OneElem dB · dB.entry.logN ≤ 64 of k12_bat_priced_chal
(Johnson/Desc/K12/Law/K12BatChal.lean [not in this library]) at dB := the place's first written
round.
EVALUATED (a run's word; the print is not in this library): batOneOk, at another text than this: at
the four proximity tests of the smaller stored example proof and at the tiny place: true at each,
both controls false at each; the same lines print «name BAT» and «work 0» at each. batFreeOk ITSELF:
IN NO RUN; a theorem wherever the written rounds are there (BatOneMade.lean: batFreeOk_made).
-/
set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf)

def batOneOn (w : WR) : Bool :=
  Fmt.dsOf w.entry w.kind == [.elem, .trits 0] && decide (w.entry.logN ≤ 64)

/-- The test. -/
def batOneOk (p : P12) : Bool := (writtenOf p.nums).any fun ws => (ws.head?).any batOneOn

/-- … and the entry asks no bits of work. -/
def batFreeOn (w : WR) : Bool := batOneOn w && w.entry.work == 0

/-- The second test. -/
def batFreeOk (p : P12) : Bool := (writtenOf p.nums).any fun ws => (ws.head?).any batFreeOn

def batOneLines (tagS : String) (p : P12) : List String :=
  match (writtenOf p.nums).bind (·.head?) with
  | some w =>
    [tagS ++ ".BATONE\tbatOneOk " ++ toString (batOneOk p) ++ "\tname " ++ w.entry.name ++
        "\tdraws " ++ toString (repr (Fmt.dsOf w.entry w.kind)) ++ "\tlogN " ++
        toString w.entry.logN ++ "\twork " ++ toString w.entry.work,
     tagS ++ ".BATONE.control.1\tone drawn element more\t" ++
        toString (batOneOn { w with entry := { w.entry with drawE := w.entry.drawE + 1 } }),
     tagS ++ ".BATONE.control.2\tone position drawn\t" ++
        toString (batOneOn { w with entry := { w.entry with poss := w.entry.poss + 1 } }),
     tagS ++ ".BATFREE\tbatFreeOk " ++ toString (batFreeOk p),
     tagS ++ ".BATFREE.control\tone bit of work asked\t" ++
        toString (batFreeOn { w with entry := { w.entry with work := w.entry.work + 1 } })]
  | none => [tagS ++ ".BATONE\tno written round"]

end H2K.First
