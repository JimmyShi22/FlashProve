-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/FirstEnd.lean: the last block of a proof file's FIRST chain: the one text for the
three chains' ends (Johnson/Desc/ChainEnd.lean) at the state that the first chain carries
(Johnson/Desc/First/State.lean: S). Definitions with code; no theorem.

"No count of claims is owed" is asked BOTH WAYS of that text's head. (i) On the record: the clause
S.closeOk: State.lean's own word for "a round may be closed": no count waits. NOT rowsOwed.isNone: S
has two forms for "no count waits", none and some 0, and `verify-on-bytes`'s test passes both.
(ii) On the plan: the last of the rounds that the blocks in front declare counts no claims. THE
ROUNDS IN FRONT ARE NEVER TYPED: firstEnd takes the very list of blocks that the chain's maker lays
in front and reads their rounds off it.

ALSO ASKED, untestedButOwnL: at the first chain's end every group's proximity test has
begun BUT THE REQUEST's OWN GROUP's, which lies open lawfully: the last chain takes the statement
over whole and tests it, and that chain's end asks "nothing is left untested" of all groups.
`verify-on-bytes` asks nothing of the statement at the first chain's end: so these four clauses ask
more than it does. With them a description in which a proximity test on the first chain never begins
is refused at this chain's own end, under a name of its own (that it HAS BEGUN is all that is asked:
a test that begins and then idles passes). WHICH GROUP IS EXEMPT IS FIXED, not
left to what the record says of W alone: it is the group that the record names as the own one, it
must be the last group of the statement (the own group is made last on this chain; the last chain's
start finds it so too), and W must be in it and in no other.

What is not claimed. That the list which firstEnd is handed is the list that stands in front of it
on the chain: that is the maker's. What the one text for the chains' ends asks beside the clause
here is that file's matter. That a yes of this block means anything is the matter of a law, and no
theorem stands in this file. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.ChainEnd
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- ASKS: nothing is left untested BUT THE OWN GROUP. The own group is the one that the record names
as such (LinFirst.own, written where the group is made); that it is the last group made on this
chain, and that W is in it and in no other, is asked first. -/
def untestedButOwnL (s : S) : ChainEnd.Clauses :=
  let e := s.firstEnd?
  let own := e.map (·.lin.own)
  [("end: the own group is the last group", own.any fun g => g + 1 == s.st.groups.size),
   ("end: W is in the own group and in no other",
    e.any fun e => (s.st.oracles[e.lin.w]?).any fun x => x.groups == [e.lin.own]),
   ("end: a proximity test has begun on every group but the own one",
    (List.range s.st.groups.size).all fun g =>
      own == some g || (s.st.groups[g]?).any (·.inRun)),
   ("end: every sampled message but the own group's members is in a tested group",
    (List.range s.st.oracles.size).all fun o =>
      (s.st.oracles[o]?).all fun x =>
        !x.sampled || (own.any fun g => (s.st.groups[g]?).any (·.members.contains o)) ||
          x.groups.any fun g => (s.st.groups[g]?).any (·.inRun))]

/-- ASKS, at the first chain's end. -/
def endAsks (s : S) : ChainEnd.Clauses :=
  ("end: no count of claims is owed", s.closeOk) :: untestedButOwnL s

/-- **The first chain's last block.** piece: its number behind the links. front: the blocks that
stand in front of it on the chain, all of them, in order. -/
def firstEnd {Cl : Type} (piece : Nat) (front : List (Block S Cl)) : Block S Cl :=
  ChainEnd.chainEnd 1 piece true (front.flatMap (·.rounds)) endAsks

end VerifiableInference.Desc.First
