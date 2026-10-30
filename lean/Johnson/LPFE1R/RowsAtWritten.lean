-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/RowsAtWritten.lean: THE SECOND READING OF THE THREE PUBLIC FILES AT WRITTEN VALUES: a
closed term. Definitions alone. A law file; no running text imports it.

`rowsFrom` (Johnson/Desc/First/Link/Law/RowsFrom.lean) takes what the second reading reads of the
planner's value. Here its four arguments are written: what the planner configured (`writtenMade`,
Johnson/Goal/Written/Made.lean); the links' open rows (25 times 1); the pending rows (13); the 26
links' arms.
  `armsW`     the 26 arms. WHENCE: an evaluator's print of (List.range 26).map (armOf Z.p.X) at the
              stored full-size example's public files (one
              value at six sets of public files, five of them in scope: evidence at six points, no
              more), pasted by program.
  `armAtW l`  the arm of link l; none beyond the list.
  `rowsW`     rowsFrom at the four written values. `rowsWB`: it returns.

Limits. THAT THE ARMS AND THE OPEN ROWS ARE THESE AT ALL FILES IN SCOPE IS SHOWN NOWHERE. Nothing is
proved here. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.RowsFrom
import Johnson.Goal.Written.Made

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open Johnson.G.MadeFree (Hung)
open VerifiableInference.PlanWritten.Joined (writtenMade)

/-- The 26 links' arms, written. -/
def armsW : List Arm :=
  [.layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := true,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005923,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .layer
     { v := 30, d := 19, shifted := true }
     { lt := 10,
       ls := 6,
       lNI := 3,
       lPd := 13,
       ll := 2,
       lPf := 14,
       lfe := 13,
       lamS := 23,
       lkW := 18,
       NI := 8,
       NS := 9,
       NP := 7,
       NO := 4,
       withTerms := true,
       shownByTheTerms := 266,
       neverSent := 3,
       weightClaims := 32,
       firstGroup := false,
       routed := true }
     { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } }
     32005793,
   .attention
     { v := 29, d := 18, shifted := true }
     { lt := 10,
       lgk := 3,
       pairs := 20,
       Lam := 4,
       planeMessages := 2,
       score := [(17, 20), (14, 20)],
       e := 13,
       valueM := 16,
       valueD := 13,
       attained := 20,
       bits := 17,
       rows := 14166783 }
     { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } },
   .head
     { v := 31, d := 19, shifted := true }
     { lt := 10, lPd := 13, lkW := 18, sums := 9, products := 7, rowValues := 4, rows := 24653737 }
     { columns := 20703, tau := 128, digits := { v := 27, d := 11, shifted := true } },
   .none]

/-- The arm of a link; none beyond the list. -/
def armAtW (l : Nat) : Arm := armsW.getD l .none

/-- The second reading at the written values. -/
def rowsW : Except String (List Johnson.G.SendRow) :=
  rowsFrom (writtenMade.at Hung.none) (List.replicate 25 1) 13 armAtW

/-- It returns. -/
def rowsWB : Bool := rowsW.toOption.isSome

end VerifiableInference.Desc.LinkJoin
