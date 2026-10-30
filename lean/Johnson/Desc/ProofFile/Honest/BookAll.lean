-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookAll.lean: the fifth of the files that compute the book of coins
(`ProverCoinCounts`, Honest/Frame.lean): one book from a description and the library's list of sendings, as far
as these functions are written: the rows of the parts that hold a sending (Honest/BookRows.lean),
all entries by which a part spends (Honest/BookEntries.lean, Honest/BookFolds.lean), and the cut
(Honest/BookOf.lean). From public data alone. It names no prover's side. An executable definition;
no theorem.

What it contains, in the book's order of entries: the first chain's segments, link by link; the
masked sumchecks of the first chain that are in no segment; the folds that spend a fresh table sent
ahead, chain by chain; the shared split's one coin.

  `Merges`   which parts are merges, and which sumchecks outside a segment spend the index-mask
     message: public data that the caller supplies, by address
  `splitEntry`   the shared split's coin: the first entry of the split's mask message
  `spendingBook`   the book

Not in it: the rows of a proximity test's switches (so the part after a test's first fold has no
coin here, and the book's third test can fail at such a place); every entry by which a part carries;
the entries of the second chain's own sendings beyond the folds'.

Limits.
  * As those of the four files that it calls.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookFolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi S Cl : Type}

/-- **What the names of rounds do not say.** -/
structure Merges where
  /-- the masked sumchecks of segments whose end values are put under the index-mask message -/
  ends : List Addr
  /-- the masked sumchecks outside a segment that spend the index-mask message alone -/
  lone : List Addr

/-- The segments' ranges, link by link; the index-mask message's next free entry is passed on. An
error where a segment's mask row is not found. -/
def linksWants (bs : List (Block S Cl)) (c : Johnson.G.ChainSends) (later : List Fmt.DeclaredRound)
    (idx : MsgAt) (merges : List Addr) : List Nat → Nat → Except String (List Want × Nat)
  | [], t => .ok ([], t)
  | l :: ls, t =>
    match ownerOf maskRowRun bs c later s!"link {l}, moment 0" isMaskRowMsg with
    | none => .error s!"segment {l}: its mask row is not found"
    | some row =>
      let x := segmentWants bs l row idx merges t
      (linksWants bs c later idx merges ls x.2).map fun y => (x.1 ++ y.1, y.2)

/-- The sumchecks outside a segment, in the chain's order. -/
def loneWants (idx : MsgAt) (lone : List Addr) : List PartAt → Nat → List Want × Nat
  | [], t => ([], t)
  | p :: ps, t =>
    let x := if lone.contains p.addr then loneSumWants idx p t else ([], t)
    let y := loneWants idx lone ps x.2
    (x.1 ++ y.1, y.2)

/-- **The shared split's coin**: the first entry of the split's mask message, which is sent with
Omega; its spender: the part that holds the round "SPLIT". `none` where there is no such round or
message. -/
def splitEntry (bs : List (Block S Cl)) (c : Johnson.G.ChainSends) : Option Ahead :=
  let i := (bs.flatMap (·.rounds)).findIdx fun r => r.entry.name == "SPLIT"
  (addrOfRound bs i).bind fun p =>
    (ownerOf splitMaskRun bs c [] "Omega" isIndexMaskMsg).map fun m =>
      (⟨p, "split", m, 0, 1⟩ : Want).entry

/-- **The book, as far as these functions are written.** `p0`, `p1`, `p2`: the library's sendings of
the proof's three chains. Where `splitEntry` returns `none` the book has no such entry, and no error
is returned. -/
def spendingBook (F : FileDescription Xi) (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    Except String ProverCoinCounts := do
  let bs := F.first.blocksInOrder
  let later := F.second.blocksInOrder.flatMap (·.rounds)
  let r0 ← rowsIn bs p0 later
  let r1 ← rowsIn F.shared.blocksInOrder p1
  let r2 ← rowsIn F.second.blocksInOrder p2
  let idx ← match ownerOf indexMaskRun bs p0 later "link 0, moment 0" isIndexMaskMsg with
    | some m => pure m
    | none => throw "the index-mask message is not found"
  let links := (bs.filterMap (·.place.link)).eraseDups
  let a ← linksWants bs p0 later idx M.ends links 0
  let b := loneWants idx M.lone
    ((bs.filter fun x => x.place.link.isNone).flatMap planParts) a.2
  if !wantsFree (a.1 ++ b.1) then throw "a stretch leaves its message's free entries, or two meet"
  let f0 ← foldEntries (planOf bs) (planOf F.second.blocksInOrder) p0
  let f1 ← foldEntries (planOf F.shared.blocksInOrder) [] p1
  let f2 ← foldEntries (planOf F.second.blocksInOrder) [] p2
  pure { first := r0, shared := r1, second := r2
         ahead := (a.1 ++ b.1).map (·.entry) ++ f0 ++ f1 ++ f2 ++
           (splitEntry F.shared.blocksInOrder p1).toList
         cuts := cutsOf F }

end ProofFile.Honest
