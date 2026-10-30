-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshDefs.lean: kind K14: THE WORDS IN WHICH THE OWNER's SENTENCE
ON THE COIN THAT "SPLIT" SPENDS IS STATED. The part that plays "send o_omega"
(Honest/K14/Sendings.lean: sendingPart at jobOmega) sends, where the shape splits, two oracle
messages: o_omega and the split's mask message o_sp. One entry of o_sp's mask row is a coin that the
part at "SPLIT" adds to its scalar. The field fresh of the structure Good (Honest/Side.lean) is the
owner's sentence on such a coin. Definitions with code, but for one proposition; no theorem.

  spMaskCode      the mask code that o_sp's shape names
  spAsked         of the positions that will be read of the part's tables: those of the tree that
                  holds o_sp
  spBud           **the bound on positions**: these positions, each modulo the mask code's length,
                  are at most as many DISTINCT numbers as the mask row's random tail has entries
  spFirstCoin     the number, among the part's own coins, of the first coin of message number 1.
                  Under the premises named in the Limits: o_sp's entry number 0; the coins in front
                  of it are o_omega's; o_sp's entries follow from it on, the pad of its
                  out-of-domain (OOD) sample last; then its random tail
  spendersOf      the entries of a book by which any part SPENDS coins of one owner
  oneSpender      **a test on the book, from the owner's side**: at most one such entry; it hands
                  over one coin of the extension field, and that coin is one of the first n entries
                  of a run that begins at a given number: so an entry of o_sp that is no pad
  knownBelow      **a second test on the book, and on the order of places**: whatever else of the
                  owner's coins of the extension field is handed to that spender, or to a part in
                  front of it, lies below a given number: so among o_omega's coins

Why two tests beside the book's own. The book's own tests (ProverCoinCounts.clauses, Honest/Frame.lean) ask that
a coin which is spent stands in no second spending entry and is handed to no part in front of its
spender. They let through an entry that hands ALL OTHER coins of o_sp to a part in front of the
spender; the spent coin is a function of these and one symbol of the row, or the answer (by reading
of a code word: no statement here says so). bookSplitFits
(Honest/K14/Thread2Full.lean) reads the entries by their spender; the owner's sentence runs over
every spender.

Limits. spFirstCoin is o_sp's entry number 0, with the order of coins as said above, WHERE THE SHAPE
SPLITS AND o_sp HAS NO MAIN ROW, ONE MASK ROW AND ONE OOD ANSWER (SpShape,
Johnson/Desc/K14/Honest/FreshAtChain.lean): where the shape does not split it is the part's whole
count, and no coin has that number. knownBelow reads the numbers of the extension field alone: the
part at hand takes no coin of the base field, and there the cut of an entry that names one is none
at all coins: AND cutAll (Honest/Frame.lean) BINDS: one such known entry makes the whole list of
known runs none at all coins, and the field fresh then says nothing of any known coin. An entry of
no coin that starts above the number is rejected.
spMaskCode is the type's default code where the list of mask codes has none at the number that
o_sp's shape names (the library's freshPublicB reads the same).
spAsked reads the first round's lists alone: the second round has no table. Where no tree
holds o_sp it is empty; IT IS EMPTY TOO WHERE asks HAS NO FIRST ROUND, OR NO LIST AT THAT TREE's
NUMBER: spBud then holds for want of a list, not for few positions. spBud says nothing on the tree
that holds o_omega alone. Nothing here says
that a book passes the tests, or that a run's positions meet the bound. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sendings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)

/-- The mask code that o_sp's shape names. -/
def spMaskCode (A : SendPub) : OnBytes.Code :=
  A.P.codes.mask.getD A.P.S.sharedSplit.maskCode default

/-- **The positions that will be read of the tree that holds o_sp**, which is message number 1 of
the sending. asks: round by round, root by root, as the frame's shownOf looks them up. -/
def spAsked (A : SendPub) (asks : List (List (List Nat))) : List Nat :=
  match ((VerifiableInference.Desc.Own.treesMade (jobOmega A).Q.codes
      (jobOmega A).Q.sent).getD {}).tree[1]? with
  | some t => (((asks[0]?).getD [])[t]?).getD []
  | none => []

/-- **The bound on positions**: it counts DISTINCT positions of the mask code's word. -/
def spBud (A : SendPub) (asks : List (List (List Nat))) : Prop :=
  (((spAsked A asks).map (· % 2 ^ (spMaskCode A).logN)).toFinset).card ≤ (spMaskCode A).r

/-- The number, among the part's own coins, of the first coin of message number 1: o_sp's entry
number 0 under the premises named in this file's Limits. -/
def spFirstCoin (A : SendPub) : Nat :=
  offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1

/-- The entries by which any part spends coins of the part at o, in the book's order. -/
def spendersOf (B : ProverCoinCounts) (o : Addr) : List Ahead := B.ahead.filter fun e => e.once && e.owner == o

/-- **At most one entry spends of the part at o**; it hands over one coin of the extension field
and none of the base field, from the base field's number 0; the coin's number is at least first and
below first + n. -/
def oneSpender (B : ProverCoinCounts) (o : Addr) (first n : Nat) : Bool :=
  match spendersOf B o with
  | [] => true
  | [e] => e.start.f == 0 && decide (first ≤ e.start.e) && decide (e.start.e < first + n) &&
      e.count == ⟨0, 1⟩
  | _ => false

/-- **Whatever else of the extension field's coins of the part at o is handed to a spender of its
coins, or to a part in front of that spender, lies below the number top.** The base field's numbers
are not read. -/
def knownBelow (B : ProverCoinCounts) (ord : List Place) (o : Addr) (top : Nat) : Bool :=
  (spendersOf B o).all fun e =>
    (B.knownBy ord o e.spender).all fun q => decide (q.start.e + q.count.e ≤ top)

end ProofFile.Honest.K14
