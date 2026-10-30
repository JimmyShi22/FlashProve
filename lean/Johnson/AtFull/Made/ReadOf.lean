-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReadOf.lean: when the readers of a chain's parameter bytes return, and what.
One law for each of six readers of OnBytes/Params/Chains.lean. General: no value is named.

Each of these readers calls `Given.read` on the bytes, matches the names of the items that it
returns, calls one reader for each item's value, and some of them ask tests at the end. Each law
here takes the return of every routine that the reader calls as a premise, and the tests' yes, and
concludes that the reader returns the value that is built of these. The library has the like for
the reader of a link's chain (`Link.read_of`, OnBytes/Params/EntryRoundsToy.lean).

  `shared_read_of`, `second_read_of`, `oneTime_read_of`, `first_read_of`: a chain's reader.
  `keyChains_read_of`, `proofChains_read_of`: the readers of a file's three chains.
  `firstTests`: the six tests at the end of `First.read`. `threeTests`: the six tests at the end of
    `KeyChains.read` and of `ProofChains.read`, which are the same. Both are the readers' own texts.

Limits. No premise is shown here at any bytes. Nothing where a routine refuses or a test says no.
Nothing on soundness.
-/
import OnBytes.Params.Chains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params

/-- Parameter bytes that hold the two items of a shared chain are read as such. -/
theorem shared_read_of {b c l : ByteArray} {g : Given} {x : Codes} {y : LinShape}
    (hg : Given.read b = some g)
    (hi : g.items = [("codes", c), ("the test on the table", l)])
    (hc : readCodes c = some x) (hl : readLin l = some y) : Shared.read b = some ⟨g, x, y⟩ := by
  unfold Shared.read
  simp only [hg, hi, hc, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- Parameter bytes without a further item are read as those of a second chain. -/
theorem second_read_of {b : ByteArray} {g : Given} (hg : Given.read b = some g)
    (hi : g.items = []) : Second.read b = some ⟨g⟩ := by
  unfold Second.read
  simp only [hg, hi, Option.bind_eq_bind, Option.bind_some, List.isEmpty_nil, if_true,
    Option.pure_def]

/-- Parameter bytes that hold the five items of a key's one-time chain are read as such. -/
theorem oneTime_read_of {b m r t c l : ByteArray} {g : Given} {x1 : OracleNotice} {x2 : WfPublic}
    {x3 : LinBindingShape} {x4 : Codes} {x5 : LinShape} (hg : Given.read b = some g)
    (hi : g.items = [("index-mask message", m), ("ranges", r), ("binding tree", t), ("codes", c),
      ("the test on the table", l)])
    (h1 : readNotice m = some x1) (h2 : readRanges r = some x2) (h3 : readBinding t = some x3)
    (h4 : readCodes c = some x4) (h5 : readLin l = some x5) :
    OneTime.read b = some ⟨g, x1, x2, x3, x4, x5⟩ := by
  unfold OneTime.read
  simp only [hg, hi, h1, h2, h3, h4, h5, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- The six tests at the end of `First.read`: one notice at the start; the links' numbers of plain
scalars are 0, .., 0, 1; one identifier and one entry of the layout for each link; a pending row; no
entry for a table's own sample in the plan. -/
def firstTests (g : Given) (s : ReqShape) (y : ReqLayout) (ids : List Nat) (n : Nat) : Bool :=
  s.atStart.length == 1 &&
    s.link.map (·.plain) == List.replicate (s.link.length - 1) 0 ++ [1] &&
    ids.length == s.link.length && y.link.length == s.link.length &&
    decide (1 ≤ n) && g.record.isNone

/-- Parameter bytes that begin with the seven items of a proof's first chain are read as such, where
the six tests say yes. -/
theorem first_read_of {b c l s y i n t : ByteArray} {more : List (String × ByteArray)} {g : Given}
    {x1 : Codes} {x2 : LinShape} {x3 : ReqShape} {x4 : ReqLayout} {x5 : List Nat} {x6 : Nat}
    {x7 : LinBindingShape} (hg : Given.read b = some g)
    (hi : g.items = ("codes", c) :: ("the test on the table", l) :: ("request's shape", s) ::
      ("layout", y) :: ("links' identifiers", i) :: ("pending rows", n) :: ("binding tree", t) ::
      more)
    (h1 : readCodes c = some x1) (h2 : readLin l = some x2) (h3 : readReq s = some x3)
    (h4 : readLayout y = some x4) (h5 : readWords i = some x5) (h6 : readWord n = some x6)
    (h7 : readBinding t = some x7) (ht : firstTests g x3 x4 x5 x6 = true) :
    First.read b = some ⟨g, x1, x2, x3, x4, x5, x6, x7, more⟩ := by
  unfold First.read
  simp only [hg, hi, h1, h2, h3, h4, h5, h6, h7, Option.bind_eq_bind, Option.bind_some]
  exact if_pos ht

/-- The six tests at the end of the readers of a file's three chains: the second and the third chain
have the first chain's settings and digest; the items "codes" and "the test on the table" have the
same bytes in the first two chains; the plans of the second and the third chain have no entry for a
table's own sample. -/
def threeTests (a b c : Given) : Bool :=
  sameSetting a b && sameSetting a c && sameItem a b "codes" &&
    sameItem a b "the test on the table" && b.record.isNone && c.record.isNone

/-- A key's three chains are read where each is read and the six tests say yes. -/
theorem keyChains_read_of {a b c : ByteArray} {p : OneTime} {q : Shared} {r : Second}
    (h1 : OneTime.read a = some p) (h2 : Shared.read b = some q) (h3 : Second.read c = some r)
    (ht : threeTests p.given q.given r.given = true) : KeyChains.read a b c = some ⟨p, q, r⟩ := by
  unfold KeyChains.read
  simp only [h1, h2, h3, Option.bind_eq_bind, Option.bind_some]
  exact if_pos ht

/-- A proof's three chains are read where each is read and the six tests say yes. -/
theorem proofChains_read_of {a b c : ByteArray} {p : First} {q : Shared} {r : Second}
    (h1 : First.read a = some p) (h2 : Shared.read b = some q) (h3 : Second.read c = some r)
    (ht : threeTests p.given q.given r.given = true) :
    ProofChains.read a b c = some ⟨p, q, r⟩ := by
  unfold ProofChains.read
  simp only [h1, h2, h3, Option.bind_eq_bind, Option.bind_some]
  exact if_pos ht

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.shared_read_of
#print axioms Johnson.AtFull.Made.second_read_of
#print axioms Johnson.AtFull.Made.oneTime_read_of
#print axioms Johnson.AtFull.Made.first_read_of
#print axioms Johnson.AtFull.Made.keyChains_read_of
#print axioms Johnson.AtFull.Made.proofChains_read_of
