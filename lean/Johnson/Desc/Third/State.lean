-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/State.lean: the last chain of a proof file: its state, its start out of the two
earlier chains' ends, and its last test. Definitions with code. No theorem.

This chain has three names: "the last chain" and "the third chain" in these files, "the second
chain" in the format (Johnson/Desc/Block.lean: the field `second`; the refusal "the second chain's
start") and in `verify-on-bytes`.

What happens at the start. Nothing is sent. The verifier takes the first chain's last statement, its
book of trees, its count of roots and its one pending row, and of the shared chain's end the
statement, the book, the shared point psi and Omega's number. It asks: the codes' message lengths
are powers of two and the shape is lawful at the codes; at the numbers that the first chain's record
names stand W and the request's own group, and there is just one pending row; both ends' codes are
the codes that the caller names; the first chain has received as many roots as its book has trees.
Then it lays the first record.

Main names:
  `plainArm`, `rootsB`, `firstStepB`: three small tests.
  `FirstOut`, `numbersOk`, `firstOutFrom`: what is taken of the first chain's end.
  `SharedOut`, `Border`, `Loc₃`, `S₃`: the state. The number of the chain's first own tree is a
    named value of the state, laid by the start.
  `start₃`, `start₃E`: the start. Only `start₃E` asks the two tests on the codes and the shape.
  `fin₃`: the last test: a proximity test has begun on every group, and every sampled message names
    a group. It is `verify-on-bytes`'s own last test (OnBytes/Iop/Ground.lean:
    Blk.requireAllTested), written out.

Limits.
(1) W's, the own group's and the mask's numbers are handed in by name, out of the first chain's own
record (Johnson/Desc/Third/Border.lean reads S.firstEnd?). What is asked of them: numbersOk; and
that a mask's number is there just where the shape sends masks ahead. WHICH WRONG NUMBERS PASS: for
W any message of W's whole shape that is a member of the group named; for the own group any unmarked
group with W's code and the own mask code that holds it; for the mask any unsampled message without
answers (one that is spent already, or lies in another tree, too: the own test's front asks more).
Only W's own number as the mask's is shown to be refused (Law/Mask.lean).
(2) Of the pending row only the row weights g are taken; its point, masks and target are dropped. No
clause looks at the own group's open rows: that g belongs to the claim from which the first chain
laid the row (Eval) is asked by nothing here.
(3) At the start the shared chain's end is tied to this file by its codes alone. (The first block
then asks of it that Omega has a place and a tree to itself in its book and is sampled there.) Not
asked anywhere in these files: that the shared chain ran under the same shape and table; that it has
ended; that it has tested Omega; that this chain's statement holds its seal. `verify-on-bytes`
(OnBytes/Iop/Lin.lean: linSecondVerify) does not ask these either; the C++ asks the seal, the shape
and the table.
(4) That the four things of the first end are a first chain's return, and those of the shared end a
shared chain's, at the same sizes, is the caller's duty.
(5) `loc.firstTree` is compared with the format's own number (FileDescription.lastChainFirstTreeNumber) nowhere. By
reading, `firstStepB`'s second clause cannot fail behind `start₃`, which lays the number that it
compares.
(6) At a shape that splits the row (Dot) the start refuses: that arm is not written; the planner
makes no such shape.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Base.DescState
import OnBytes.Params.DeriveLin
import Johnson.Desc.Step

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open Desc.Plain (DState)

namespace VerifiableInference.Desc.Third

/-! ## Three small tests -/

/-- The shape does not split the row (Dot). -/
def plainArm (S : Params.LinShape) : Bool := !S.ownSplitNeeded

/-- At the first chain's end it has received as many roots as its book has trees. -/
def rootsB (roots : Nat) (B : TreeBook) : Bool := roots == B.trees.size

/-- In front of the taking-over: this chain has received no root, and the one tree that is about to
be taken over is the one that the number of the chain's first own tree counts. -/
def firstStepB (roots firstTree : Nat) (B : TreeBook) : Bool :=
  roots == 0 && B.trees.size + 1 == firstTree

/-! ## What is taken of the first chain's end -/

/-- What the third chain takes of the first chain's end, as one value. -/
structure FirstOut where
  st : Statement
  book : TreeBook
  /-- the roots received on the first chain -/
  roots : Nat
  /-- the claim's row weights, behind the batching -/
  g : List Tensor
  /-- the numbers of W and of the request's own group -/
  w : Nat
  own : Nat
  /-- the mask of the own test's first fold, if it went out with W -/
  mask : Option Nat

/-- What is asked of the numbers, on public things alone: the message at W's number has W's shape
and is a member of the own group; that group has W's code and the own mask code, and its test has
not begun; the mask has no sample by its shape and is not sampled. -/
def numbersOk (S : Params.LinShape) (f : FirstOut) : Bool :=
  match f.st.oracles[f.w]?, f.st.groups[f.own]? with
  | some x, some G =>
    decide (x.shape = S.w) && G.members.contains f.w && G.code == S.w.code &&
      G.maskCode == S.ownMaskCode && !G.inRun &&
      (match f.mask with
        | none => true
        | some m =>
          match f.st.oracles[m]? with
          | some y => !y.sampled && y.shape.answers == 0
          | none => false)
  | _, _ => false

/-- FirstOut out of the first chain's statement, book, roots received and list of pending rows, and
the numbers of W, of the own group and of the mask, which the caller hands in by name, out of the
first chain's own record. Nothing unless the shape does not split the row (Dot), a mask's number is
handed in just where the shape sends masks ahead, there is just one pending row, and numbersOk holds
at the three numbers. Of the pending row only g is kept. -/
def firstOutFrom (S : Params.LinShape) (st : Statement) (book : TreeBook) (roots : Nat)
    (w own : Nat) (mask : Option Nat) (pending : List TensorRow) : Option FirstOut :=
  match pending with
  | [r] =>
    if plainArm S && mask.isSome == S.masksAhead then
      let f : FirstOut :=
        { st := st, book := book, roots := roots, g := r.g, w := w, own := own, mask := mask }
      if numbersOk S f then some f else none
    else none
  | _ => none

/-! ## The state -/

/-- What the third chain takes of the shared chain's end, as one value. -/
structure SharedOut where
  st : Statement
  book : TreeBook
  /-- the shared point -/
  psi : List E
  /-- Omega's number there -/
  omega : Nat

/-- What the first step alone reads. -/
structure Border where
  g : List Tensor
  shared : SharedOut

/-- The third chain's named values. -/
structure Loc₃ where
  w : Nat
  own : Nat
  mask : Option Nat
  /-- there until the first step has run -/
  border : Option Border
  /-- Omega's number here: written by the first step -/
  omega : Nat
  /-- the number of the first tree that this chain sends: the first chain's roots + 1, since one
  tree is taken over before anything is sent (OnBytes/Iop/Ground.lean:1659-1660;
  OnBytes/Proof/Tail.lean:134-136). The start lays it; no block of these files changes it. -/
  firstTree : Nat

/-- The third chain's carried state. The opened columns are no part of it: they are a step's own
argument. -/
structure S₃ where
  st : Statement
  book : TreeBook
  /-- the roots received so far on this chain -/
  roots : Nat
  loc : Loc₃

/-- The state in the form that the plain ground's functions take: the columns laid in. -/
def S₃.withCols (s : S₃) (cols : List OpenedColumn) : DState Loc₃ :=
  { st := s.st, book := s.book, roots := s.roots, opened := cols, loc := s.loc }

/-! ## The start -/

/-- The third chain's first state. Nothing unless both ends have just these codes and the first
chain has received as many roots as its book has trees. No root has been received on this chain. The
book is the first chain's as it is. `verify-on-bytes` turns each tree's source at this point
(OnBytes/Proof/Tail.lean:140-142); on a view no source is read (OnBytes/Iop/Ground.lean:1517 stands
in the dry arm). So the first chain's trees and this chain's own both bear "own n", counted from 0:
in this book a source does not name a tree. -/
def start₃ (codes : Codes) (f : FirstOut) (o : SharedOut) : Option S₃ :=
  if decide (f.st.codes = codes) && decide (o.st.codes = codes) && rootsB f.roots f.book then
    some
      { st := f.st, book := f.book, roots := 0
        loc :=
          { w := f.w, own := f.own, mask := f.mask, border := some { g := f.g, shared := o }
            omega := noId, firstTree := f.roots + 1 } }
  else none

/-- The same with a reason in words, out of the four things of the first chain's last state. It asks
first, itself, that the codes' message lengths are powers of two and that the shape is lawful at the
codes (linOk). So whoever starts by `start₃E` cannot walk past these two tests; `start₃` asks
neither. -/
def start₃E (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ : Nat) (w₁ own₁ : Nat) (mask₁ : Option Nat)
    (pile₁ : List TensorRow) (o : SharedOut) : Except String S₃ :=
  if !(codes.lengthsOk && linOk codes S) then .error "the shape is not lawful at the codes" else
  match firstOutFrom S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ with
  | none => .error "the first chain's end gives no W, own group and one pending row"
  | some f =>
    match start₃ codes f o with
    | none => .error "the two ends' codes or the first chain's count of roots"
    | some s₀ => .ok s₀

/-- The last test: the test of every group has begun, and every sampled message is in a group: over
the whole statement, the first chain's groups and messages too. The chain's end
(Johnson/Desc/Third/Chain.lean) asks this and more: that the group named is there and is tested. -/
def fin₃ (s : S₃) : Bool :=
  s.st.groups.all (·.inRun) && s.st.oracles.all fun x => !x.sampled || !x.groups.isEmpty

end VerifiableInference.Desc.Third
