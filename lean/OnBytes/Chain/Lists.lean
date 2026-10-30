-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Lists.lean: two functions on lists as loops, and the conditions on a description
with them.

By their definitions `List.zip` and `List.sum` call themselves once for each member before they
return. The core library puts loops in the place of many functions on lists when they are compiled
(`List.map`, `List.foldr`, `List.takeWhile` and `++` among them), but, in the Lean version of this
library, not of these two: compiled, each calls itself once for each member, and in runs a list of
some hundred thousand members ended the program with a stack overflow. A chain's rounds grow with
the model. So here both are loops by definition, proved equal to the functions of the library.
The strict reader (`Fmt.readChainX`) is told a chain's description (`Fmt.SpecX`: label, plan,
rounds, opened trees). Its conditions on a description (`Fmt.SpecX.ok`) use both functions over
the rounds; they are stated once more with the loops and proved to be the same.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `zipT`, `sumT`, `roundOk`, `roundsOkT`, `specOk`, `specXOk`.
Main theorems: `zipT_eq`, `sumT_eq`, `specOk_eq`, `specXOk_eq`.
-/
import Fmt.Rules8X

namespace OnBytes

/-- Appends the pairs of the two lists' members to acc, up to the end of the shorter list. -/
def zipLoop {α β : Type} : List α → List β → Array (α × β) → List (α × β)
  | a :: as, b :: bs, acc => zipLoop as bs (acc.push (a, b))
  | _, _, acc => acc.toList

/-- `zipLoop` returns the members of acc followed by what `List.zip` returns. -/
theorem zipLoop_eq {α β : Type} : ∀ (as : List α) (bs : List β) (acc : Array (α × β)),
    zipLoop as bs acc = acc.toList ++ as.zip bs
  | [], _, acc => by simp [zipLoop]
  | _ :: _, [], acc => by simp [zipLoop]
  | a :: as, b :: bs, acc => by
    rw [zipLoop, zipLoop_eq as bs]
    simp

/-- `List.zip` as a loop. -/
def zipT {α β : Type} (as : List α) (bs : List β) : List (α × β) := zipLoop as bs #[]

/-- `zipT` equals `List.zip`. -/
theorem zipT_eq {α β : Type} (as : List α) (bs : List β) : zipT as bs = as.zip bs := by
  unfold zipT
  rw [zipLoop_eq]
  rfl

/-- The sum of a list of numbers, as a loop. -/
def sumT (l : List Nat) : Nat := l.foldl (· + ·) 0

/-- Adding up a list from the start a gives a plus the list's sum. -/
theorem foldl_add : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.sum
  | [], a => rfl
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add l, List.sum_cons, Nat.add_assoc]

/-- `sumT` equals `List.sum`. -/
theorem sumT_eq (l : List Nat) : sumT l = l.sum := by
  unfold sumT
  rw [foldl_add, Nat.zero_add]

/-- The conditions on one round: the text of `Fmt.Round.ok`, with the bytes of the message's items
summed by the loop. `noRand`: the chain has no random bytes. `after`: the round before this one
was a round of seeds. `sent`: the number of roots sent before this round. The clauses, in order:
 - the message's items have the entry's bytes, roots and answers; the entry counts one round;
 - at most 64 bits of work, and none where the verifier's message is empty or a seal (format page,
   R5.3);
 - a nonce in a file has 1 to 8 bytes, also where no round has work (R8.2);
 - answers are the first items of the message after a round of seeds and occur nowhere else
   (R8.3): no message of the verifier lies between a seed and its answers;
 - in a joining round the last item is an element of the extension field, the sum that is joined
   (R8.4): meant to fix the sum before the prover knows the drawn element;
 - a root is not sent before an empty message of the verifier or before a seal (R8.5), nor on a
   chain without random bytes (R4.5 (c));
 - positions are drawn below 2 ^ logN with logN < 64, and a listed position fits its bytes
   (R8.10);
 - openings need a draw of positions; the chain's own trees are opened by increasing number
   (R8.7);
 - no opened tree is deeper than logN; an own tree's root has been sent, its number is firstTree
   plus its place in the order of sending (R7.13), it is not a stored tree, and the chain has
   random bytes; a root and a start given from outside have 32 bytes each.
Not tested: that the number of answers is what the seeds ask for (R8.3: a condition on plans). -/
def roundOk (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) (after : Bool) (sent : Nat)
    (r : Fmt.Round) : Bool :=
  sumT (r.items.map Fmt.Item.bytes) == r.entry.msg &&
  Fmt.countItem .root r.items == r.entry.roots &&
  Fmt.countItem .answer r.items == r.entry.answers &&
  r.entry.count == 1 && r.entry.work ≤ 64 &&
  ((r.kind != .nothing && r.kind != .sealed) || r.entry.work == 0) &&
  1 ≤ P.nonce && P.nonce ≤ 8 &&
  (r.items.take r.entry.answers).all (· == .answer) && (after || r.entry.answers == 0) &&
  (r.kind != .join || r.items.getLast? == some .e) &&
  (r.entry.roots == 0 || (r.kind != .nothing && r.kind != .sealed && !noRand)) &&
  r.entry.logN < 64 && (r.entry.poss == 0 || P.posB == 0 || r.entry.logN ≤ 8 * P.posB) &&
  (r.opens.isEmpty || 0 < r.entry.poss) &&
  Fmt.increasing (r.opens.filterMap fun o => match o.2 with
    | .own n => some n
    | .given _ _ => none) &&
  r.opens.all fun o => o.1.a ≤ r.entry.logN && (match o.2 with
    | .own n => n < sent + r.entry.roots && o.1.tree == firstTree + n && !o.1.stored && !noRand
    | .given root start => root.size == 32 && start.size == 32)

/-- `roundOk` equals `Fmt.Round.ok`. -/
theorem roundOk_eq (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) (after : Bool) (sent : Nat)
    (r : Fmt.Round) :
    roundOk P noRand firstTree after sent r = r.ok P noRand firstTree after sent := by
  unfold roundOk Fmt.Round.ok
  rw [sumT_eq]
  rfl

/-- The conditions on all rounds: the text of `Fmt.roundsOk`. The Bool says whether the round
before the list's first was a round of seeds, the Nat how many roots were sent before it. -/
def roundsOkT (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    Bool → Nat → List Fmt.Round → Bool
  | _, _, [] => true
  | after, sent, r :: rs =>
    roundOk P noRand firstTree after sent r &&
      roundsOkT P noRand firstTree (r.kind == .seeds) (sent + r.entry.roots) rs

/-- `roundsOkT` equals `Fmt.roundsOk`. -/
theorem roundsOkT_eq (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
    roundsOkT P noRand firstTree after sent rs = Fmt.roundsOk P noRand firstTree after sent rs
  | [], _, _ => rfl
  | r :: rs, after, sent => by
    rw [roundsOkT, Fmt.roundsOk, roundOk_eq, roundsOkT_eq P noRand firstTree rs]

/-- The conditions on a description that do not look at a file: the text of `Fmt.Spec.ok`, with
the sums made by the loop. The clauses, in order:
 - nothing that is hashed is longer than the hash admits (`Fmt.Spec.small`; format page, R2.7);
 - the parameter bytes begin with the format's version, this plan and this configuration's digest
   (R4.3): meant to make the chain's first value bind what the reader follows;
 - the plan is in order, and the rounds' entries are `S.plan.rounds`;
 - each entry has its kind's draws and no others (R6.2);
 - random bytes that are given have 32 bytes, and so has the configuration's digest;
 - the chain has at least one round (a condition of Fmt/, on which the format page is silent);
 - firstTree and the number of roots that the chain sends come to less than 2 ^ 16, and every
   opened tree's number is below 2 ^ 16 (R7.13 bounds the places of a chain's list of trees and
   admits exactly 2 ^ 16; this clause of `Fmt.Spec.ok` does not. A tree that the chain takes over is
   counted only as far as the description's firstTree counts it: Chan.firstTree,
   OnBytes/Iop/Ground.lean);
 - a tree of the chain's own that is opened more than once has one shape;
 - each round is in order (`roundsOkT`);
 - no opened tree is deeper than the format admits (`Fmt.depthOK`; R7.16);
 - the plan's length of a salt is one of the format's, also where no round has an opening (R7.3).
Not tested: the chain's label. `Fmt.startChainW` refuses a label that is not below 2 ^ 32. -/
def specOk (S : Fmt.Spec) : Bool :=
  S.small &&
  S.params.extract 0 (Fmt.paramsBytes S.plan S.cfg []).size == Fmt.paramsBytes S.plan S.cfg [] &&
  S.plan.ok && S.rounds.map (·.entry) == S.plan.rounds &&
  (S.rounds.all fun r => r.entry.fits r.kind S.plan.samples) &&
  (match S.rand with
    | .given b => b.size == 32
    | _ => true) &&
  S.cfg.size == 32 &&
  !S.rounds.isEmpty &&
  S.firstTree + sumT (S.rounds.map (·.entry.roots)) < 2 ^ 16 &&
  (S.rounds.all fun r => r.opens.all fun o => o.1.tree < 2 ^ 16) &&
  (S.ownShapes.all fun x => S.shapeOf x.1 == some x.2) &&
  roundsOkT S.plan S.rand.isNone S.firstTree false 0 S.rounds &&
  (S.rounds.all fun r => r.opens.all fun o => Fmt.depthOK o.1.a) &&
  Fmt.saltLenOK S.plan.salt

/-- `specOk` equals `Fmt.Spec.ok`. -/
theorem specOk_eq (S : Fmt.Spec) : specOk S = S.ok := by
  unfold specOk Fmt.Spec.ok
  rw [sumT_eq, roundsOkT_eq]
  rfl

/-- The conditions on a description with stored trees that do not look at a file: the text of
`Fmt.SpecX.ok`, with the rounds and their stored trees paired by the loop. The description without
stored trees is in order (`specOk`); there is one list of stored trees for each round; each list
meets `Fmt.storedOk`. By `Fmt.storedOk` a round that opens stored trees opens no other tree, and
the stored trees' parts use up all the round's draws. -/
def specXOk (S : Fmt.SpecX) : Bool :=
  specOk S.base && S.stored.length == S.base.rounds.length &&
    (zipT S.base.rounds S.stored).all fun x => Fmt.storedOk S.base.statement x.1 x.2

/-- `specXOk` equals `Fmt.SpecX.ok`. -/
theorem specXOk_eq (S : Fmt.SpecX) : specXOk S = S.ok := by
  unfold specXOk Fmt.SpecX.ok
  rw [specOk_eq, zipT_eq]

end OnBytes
