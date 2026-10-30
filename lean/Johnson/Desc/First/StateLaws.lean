-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/StateLaws.lean: WHAT TIES State.lean's OWN TEXTS TO THE ROUTINES OF THE
PROGRAM `verify-on-bytes`. Theorems alone; no definition. It stands BESIDE State.lean, so that the
description's own file names no test of that program where it has a text of its own.

What is said. `S.coveredAt_eq`: the covered positions in State.lean's own text are the routine
`Head.coveredOf` of `verify-on-bytes` (OnBytes/Model/HeadLayout.lean), verdict, refusal's name and
value, at every T, V, reply and state: so whatever stood on that call stands. `S.call_eq_callE`: of
the two tools of stand-ins, call is callE with the reason dropped.

Limits. That the start in plain text (`S.startP`) is the start by `verify-on-bytes`'s
`ChainCheck.start` stands in a file of its own, not here. `S.call` and `S.callE` run whatever
routine they are handed.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

namespace S

/-- call is callE with the reason dropped. -/
theorem call_eq_callE {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (cols : List Col) (b : Blk α) :
    s.call P es rs cols b = (s.callE P es rs cols b).toOption := by
  unfold call callE
  cases b (s.ctx P es rs cols) with
  | error f => rfl
  | ok p =>
    cases p with
    | mk a c =>
      dsimp only
      generalize (c.ch.cur.isNone && c.ch.entries.isEmpty && c.ch.left.isEmpty &&
        decide (c.ch.opened.length ≤ cols.length)) = t
      cases t <;> rfl

/-- The covered positions in State.lean's own text are the routine of `verify-on-bytes`. -/
theorem coveredAt_eq (T V y : Nat) (s : S) :
    s.coveredAt T V y = Head.coveredOf { req := s.req, r := s.rowR, e := s.rowE, y := y } T V := by
  unfold coveredAt Head.coveredOf Head.needed
  dsimp only [bind, Except.bind, pure, Except.pure]
  generalize decide (y < V) = b1
  generalize (s.req.size == T + 2) = b2
  generalize (((s.req.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = b3
  generalize (decide ((s.req.getD T 0).toNat ≥ (s.req.getD (T + 1) 0).toNat) ||
    decide ((s.req.getD (T + 1) 0).toNat > T)) = b4
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

end S

end VerifiableInference.Desc.First
