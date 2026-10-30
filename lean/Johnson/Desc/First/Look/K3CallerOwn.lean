-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerOwn.lean: the clause of the condition in front of the lookup that
ties the caller's data D (K3Caller.lean: Sent) to the record that the first chain carries
(Johnson/Desc/First/State.lean: S). Two definitions and one small statement. No soundness is
claimed.

Why. The caller's signature and its reading msg₀ are made of the chain's codes, the request's shape,
the layout and the link's arrayOf. The public record Verify.Public holds none of the four. They
stand in the carried record, and it is from there that the link's closing takes them when it turns
the link's one equation into a row on oracle messages. So «the record's own four are D's» makes the
caller's reading the closing's; and a made-up D is met by no record that a run carries.

Main names.
  ownOf s: inside a link: the record's codes, the live state of the calls' shape and layout, the
    link's number and its arrayOf. None between two links.
  OwnIs D i s: ownOf s is D's five at link i.
  ownIs_inj: two D with OwnIs at one record and one link have the same codes, shape, layout and the
    same arrayOf at that link.
Limits. That the carried record's four are those of the chain's parameter bytes is the start's duty
(S.start?) and the fold's: not here. Plain records and pure functions alone are named (S, S.link?,
S.live, LinkCtx, ChainCheck, ReqFrame, ReqRows).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Look.K3Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The carried record's own five, inside a link. -/
def ownOf (s : First.S) :
    Option (Codes × Params.ReqShape × Params.ReqLayout × Nat × Array (Nat × String)) :=
  s.link?.map fun L => (s.st.codes, s.live.frame.shape, s.live.rows.layout, L.link, L.arrayOf)

/-- D's five at link i. -/
def Sent.five (D : Sent) (i : Nat) :
    Codes × Params.ReqShape × Params.ReqLayout × Nat × Array (Nat × String) :=
  (D.codes, D.shape, D.layout, i, D.arrayOf.getD i #[])

/-- **The record's own are D's.** -/
def OwnIs (D : Sent) (i : Nat) (s : First.S) : Prop := ownOf s = some (D.five i)

theorem ownIs_inj {D D' : Sent} {i : Nat} {s : First.S} (h : OwnIs D i s) (h' : OwnIs D' i s) :
    D.five i = D'.five i := Option.some.inj (h.symm.trans h')

#print axioms ownIs_inj

end VerifiableInference.Desc.First.Look
