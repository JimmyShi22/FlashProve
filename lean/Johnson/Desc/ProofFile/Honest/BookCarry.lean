-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookCarry.lean: the eighth of the files that compute the book of coins
(`ProverCoinCounts`, Honest/Frame.lean): the entries by which a part carries: which oracle messages' coins a
fold, and the part that sends what the fold leaves, are given. From the declared rounds' names and
the library's list of sendings alone. It names no prover's side. Executable definitions, and tests
at synthetic lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

Why a fold carries at all. A part is given no table, and what parts pass on holds no coin. A fold
sums over the messages of its group's rows, and the part after it sends what the fold leaves: the
folded rows' messages and random tails (`switchParts`, OnBytes/Iop/Cs.lean). So both must compute
these rows again, from the input and from the coins of every oracle message of the group.
Why, in the chain of segments, it carries all that was sent before. From the second segment on a
group holds the carrying message, whose rows hold what the fold before has left: that reads every
coin of the group before and of that fold's fresh table; and so on, back to the first segment. This
was found by the authors of two kinds' parts (K10 and K2), not by this file's: its author had listed
one group alone. What is this file's own: the list is read from another source than theirs: the
labels of `Johnson.G.sendsOf`.

The rule, for each fresh table that is sent ahead, with p the fold that spends it and q the part
that holds the first round "SEND seed" after that fold:
  to p   every message of the fold's reach but that fresh table (p spends its coefficients)
  to q   the same, and that fresh table
The order counts: `lend` (Honest/Frame.lean) goes through a part's own list `carries` and the book's
entries for that part in step, comparing the names first. In the chain of segments the entries of q
are in the order of sending, the fold's fresh table in its place: where it was sent, before its
link's later sendings: as the authors of K2's part list what it carries (Honest/K2/Seat.lean,
`sentBy`). Elsewhere (`carryPair`): the group, then the fresh table.
The reach. In the chain of segments, of the fold of group l: all messages of the sendings "link j,
.." with j at most l, the fresh tables among them; not the index-mask message, which is in no
segment's group. Elsewhere the group alone (docs/format/09-key-and-leaf-files.md, its terms): the
folded row's: the folded row and the shared split's mask message; Omega's: Omega and that message; a
request's own: the index-mask message, W with what is sent with it, and Omega.

  1  `SentMsg`, `sentIn`, `linkOf`, `SentMsg.carry`   the messages of a chain's sendings, each with
     its whole range
  2  `behindFold`, `carryPair`   p and q; the entries of one fold
  3  `segmentCarries`   the chain of segments
  4  `groupCarries`   a fold elsewhere: the caller supplies the group

Limits.
  * A fold that sends its own fresh table has no entry for that table here.
  * `fresh` and `masks` are read off a message's shape (`isFresh`, Honest/BookRows.lean;
    `isIndexMaskMsg`, Honest/BookEntries.lean). They mean a fold's fresh table and the index-mask
    kind only at a list of sendings that `Johnson.G.sendsOf` has returned; the list is a free
    argument here.
  * That the first fold after a sending spends its fresh table is assumed, as in
    Honest/BookFolds.lean.
  * What a part really reads of a range is for its author to say.
  * `sentIn` takes the number k of a fold's rounds as `(foldK …).getD 0`: where no fold follows a
    sending, k is 0, and a fresh table in that sending is counted at one coefficient; `sentIn`
    returns no error there. `rowsIn` (Honest/BookRows.lean) and `foldEntries`
    (Honest/BookFolds.lean) do.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookFolds
import Johnson.Desc.ProofFile.Honest.BookCoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-! ## 1 The messages -/

/-- An oracle message of a sending that is no switch: the sending's label and round, the part that
holds it, the message's number in the sending, its whole range among that part's coins. -/
structure SentMsg where
  label : String
  round : Nat
  sender : Addr
  j : Nat
  start : Due
  count : Due
  /-- a fold's fresh table -/
  fresh : Bool
  /-- mask rows alone, with a sample: the index-mask message; a split's mask message -/
  masks : Bool

/-- **The messages of a chain's sendings**, in the order of sending. `later`: as `rowsIn` takes it.
Where no fold follows, k is taken as 0; `rowsIn` returns an error there. -/
def sentIn (bs : List (Block S Cl)) (c : Johnson.G.ChainSends) (later : List Fmt.DeclaredRound := []) :
    Except String (List SentMsg) :=
  if (seedRounds bs).length != c.sends.length then
    .error "the sendings are not as many as the chain's rounds SEND seed"
  else
    List.flatten <$> (((seedRounds bs).zip c.sends).filter fun x => !isSwitch x.2.label).mapM
      fun (x : Nat × Johnson.G.Sending) =>
      let k := (foldK ((bs.flatMap (·.rounds) ++ later).drop (x.1 + 1))).getD 0
      x.2.sent.zipIdx.mapM fun (n : OnBytes.OracleNotice × Nat) =>
        (match addrOfRound bs x.1, msgStretch c.codes k x.2.sent n.2 with
          | some a, some st =>
            Except.ok ⟨x.2.label, x.1, a, n.2, st.1, st.2, isFresh n.1, isIndexMaskMsg n.1⟩
          | _, _ => Except.error (x.2.label ++ ": an address or a code is lacking") :
          Except String SentMsg)

/-- The number l in a label "link l, moment m". -/
def linkOf (label : String) : Option Nat :=
  match label.splitOn ", moment " with
  | [a, _] => if a.startsWith "link " then (a.drop 5).toNat? else none
  | _ => none

/-- The entry by which the part at `dest` carries the message. -/
def SentMsg.carry (m : SentMsg) (dest : Addr) : Ahead :=
  ⟨carriedName m.sender m.j dest, m.sender, m.start, m.count, dest, false⟩

/-! ## 2 One fold -/

/-- **The fold after round number i, and the part that sends what it leaves**: the part that holds
the first "FOLD epsilon" after i, and the part that holds the first "SEND seed" after that. -/
def behindFold (l : List PlanB) (i : Nat) : Option (Addr × Addr) :=
  (foldBehind l i).bind fun f =>
    let rs := (l.flatMap (·.rounds)).zipIdx.drop (f.1 + 1)
    ((rs.find? fun r => r.1.entry.name == "SEND seed").bind fun s => addrIn l s.2).bind fun q =>
      (addrIn l f.1).map fun p => (p, q)

/-- **One fold's entries.** `reach`: the messages of its reach, without its own fresh table. `own`:
that table, where it was sent ahead. -/
def carryPair (p q : Addr) (reach : List SentMsg) (own : Option SentMsg) : List Ahead :=
  reach.map (·.carry p) ++ (reach ++ own.toList).map (·.carry q)

/-! ## 3 The chain of segments -/

/-- **The carrying entries of the chain of segments.** `ms`: the chain's messages, in the order of
sending. For the fresh table f of link l: to p, the fold: the messages of the links below l, and
those of link l but its fresh table. To q, the part that sends what the fold leaves: all messages of
the links up to l, in the order of sending: so f is where it was sent, before link l's later
sendings. The index-mask kind goes to neither. A link is taken to have one fresh table: with two, q
is given both at each of the two; where both have one q its entries are then there twice under one
name, which the book's own test on names rejects (`ProverCoinCounts.clauses`, the last). -/
def segmentCarries (here : List PlanB) (ms : List SentMsg) : Except String (List Ahead) :=
  List.flatten <$> (ms.filter fun m => m.fresh && (linkOf m.label).isSome).mapM
    fun (f : SentMsg) =>
    (match behindFold here f.round, linkOf f.label with
      | some (p, q), some l =>
        Except.ok
          ((ms.filter fun m => !m.masks && ((linkOf m.label).any fun j =>
            decide (j < l) || (j == l && !m.fresh))).map (·.carry p) ++
          (ms.filter fun m => !m.masks && ((linkOf m.label).any fun j =>
            decide (j ≤ l))).map (·.carry q))
      | _, _ => Except.error (f.label ++ ": no fold, or no sending, stands behind its table") :
      Except String (List Ahead))

/-! ## 4 A fold elsewhere -/

/-- **The carrying entries of a fold whose group the caller supplies.** `i`: a round before the
fold, after every fold before it. -/
def groupCarries (l : List PlanB) (i : Nat) (group : List SentMsg) (own : Option SentMsg) :
    Except String (List Ahead) :=
  match behindFold l i with
  | some (p, q) => .ok (carryPair p q group own)
  | none => .error "no fold, or no sending, stands behind the round"

/-! ### Tests at synthetic lists -/

#guard linkOf "link 12, moment 0" == some 12 && linkOf "W" == none &&
  linkOf "the own test, the code switch of stage 2" == none

/-- Two segments and a last test: in each a sending, a closing; the last test has a switch. -/
def toyChain : List PlanB :=
  [⟨⟨1, some 0, 1, .K1⟩, [1], [rd "SEND seed" 1]⟩,
   ⟨⟨1, some 0, 2, .K10⟩, [2], [rd "FOLD epsilon", rd "FOLD round"]⟩,
   ⟨⟨1, some 1, 1, .K2⟩, [1], [rd "SEND seed" 1]⟩,
   ⟨⟨1, some 1, 2, .K10⟩, [2], [rd "FOLD epsilon", rd "FOLD round"]⟩,
   ⟨⟨1, none, 1, .K2⟩, [1], [rd "SEND seed" 1]⟩]

def sm (label : String) (round piece j : Nat) (link : Option Nat) (fresh masks : Bool := false) :
    SentMsg :=
  ⟨label, round, ⟨⟨1, link, piece, .K1⟩, 0⟩, j, ⟨0, j⟩, ⟨0, 1⟩, fresh, masks⟩

/-- The first sending: a message, the fresh table, the index-mask message. The second: the carrying
message, a message, the fresh table. -/
def toyMsgs : List SentMsg :=
  [sm "link 0, moment 0" 0 1 0 (some 0), sm "link 0, moment 0" 0 1 1 (some 0) true,
   sm "link 0, moment 0" 0 1 2 (some 0) false true,
   sm "link 1, moment 0" 3 1 0 (some 1), sm "link 1, moment 0" 3 1 1 (some 1),
   sm "link 1, moment 0" 3 1 2 (some 1) true]

#guard behindFold toyChain 0 == some (⟨⟨1, some 0, 2, .K10⟩, 0⟩, ⟨⟨1, some 1, 1, .K2⟩, 0⟩)
-- the first closing: one message; the second segment's sender: it and the fresh table. The second
-- closing: these two and its own group's two; the part after it: these four and the second fresh
-- table. The index-mask message goes to nobody
#guard ((segmentCarries toyChain toyMsgs).toOption.map fun l => l.map fun e =>
    (e.spender.place.link, e.spender.place.piece, e.owner.place.link, e.start.e)) ==
  some [(some 0, 2, some 0, 0), (some 1, 1, some 0, 0), (some 1, 1, some 0, 1),
    (some 1, 2, some 0, 0), (some 1, 2, some 0, 1), (some 1, 2, some 1, 0), (some 1, 2, some 1, 1),
    (none, 1, some 0, 0), (none, 1, some 0, 1), (none, 1, some 1, 0), (none, 1, some 1, 1),
    (none, 1, some 1, 2)]
#guard ((segmentCarries toyChain toyMsgs).toOption.map fun l => l.all (!·.once)) == some true
-- without a sending after the last closing: an error
#guard (segmentCarries (toyChain.take 4) toyMsgs).toOption.isNone

/-- The same messages, and a later sending of the first segment (its moment 1, at piece 4). -/
def toyMoments : List SentMsg :=
  toyMsgs.take 3 ++ [sm "link 0, moment 1" 1 4 0 (some 0)] ++ toyMsgs.drop 3

-- the order, at the second segment's sender (owner's piece, the message's start): the first
-- segment's message, its fresh table, then the later sending's message: the order of sending. (With
-- the fresh table put last this line fails.)
#guard ((segmentCarries toyChain toyMoments).toOption.map fun l =>
    (l.filter fun e => e.spender == ⟨⟨1, some 1, 1, .K2⟩, 0⟩).map fun e =>
      (e.owner.place.piece, e.start.e)) == some [(1, 0), (1, 1), (4, 0)]
-- the first closing is given the two messages, not its fresh table
#guard ((segmentCarries toyChain toyMoments).toOption.map fun l =>
    (l.filter fun e => e.spender == ⟨⟨1, some 0, 2, .K10⟩, 0⟩).map fun e =>
      (e.owner.place.piece, e.start.e)) == some [(1, 0), (4, 0)]
-- the part after the second closing: the earlier segment in the order of sending too
#guard ((segmentCarries toyChain toyMoments).toOption.map fun l =>
    (l.filter fun e => e.spender == ⟨⟨1, none, 1, .K2⟩, 0⟩).map fun e =>
      (e.owner.place.link, e.owner.place.piece, e.start.e)) ==
  some [(some 0, 1, 0), (some 0, 1, 1), (some 0, 4, 0), (some 1, 1, 0), (some 1, 1, 1),
    (some 1, 1, 2)]

end ProofFile.Honest
