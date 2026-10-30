-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Trees.lean: how the oracle messages of one prover's message are placed in trees, as
a named part of the description, for every block that receives oracle messages.

Messages of one leaf class whose main rows have one length share a tree. A message without main rows
joins the first tree of its class or, if there is none, opens a tree of its own.

  treeOfPass codes sent maskOnly s
      ONE PASS OVER THE MESSAGES, in the order of sending. maskOnly = false: the messages that have
      main rows; maskOnly = true: those that have none. The state s: the trees so far; each tree's
      leaf class; for each message the number of its tree. A message goes to the first tree of its
      class (for a message with main rows: of its class and of its main rows' length); if there is
      none it opens a new tree. It cannot fail.
  treeOf codes sent
      BOTH PASSES: first the messages with main rows, then the others.
  fillStep codes sent tree s i
      MESSAGE NUMBER i IS LAID INTO ITS TREE. The state s: the trees; for each message so far its
      place among its tree's parts; for each tree the width of its mask symbols so far. IT GIVES
      NOTHING IF the message has mask rows, its tree holds mask symbols already, and these are of
      another length than the message's. Else the tree takes the message's mask length (if it has
      mask rows) and the numbers of its main and mask symbols in a column.
  closeTrees tree filled
      THE LAST STEP. A tree without main symbols gets its mask rows' length as its length. IT GIVES
      NOTHING IF some tree holds mask symbols and their length exceeds the tree's.
  treesMade codes sent
      THE WHOLE: the trees by treeOf; every message laid by fillStep, in the order of sending; then
      closeTrees.
  treesCan codes sent
      THE TREES CAN BE LAID: treesMade gives something.
THE TWO PLACES AT WHICH IT SAYS NO, AND THERE ARE NO OTHERS, AND WHAT EACH REFUSAL CHECKS. A tree
has 2 ^ logN leaves; the leaf of position x holds the main rows' symbols at x and, after them, the
mask rows' symbols at x modulo the tree's ONE mask length 2 ^ logNzk. (1) A message with mask rows
comes into a tree that already holds mask symbols of another mask length (fillStep): the tree
records one mask length, so the rows of a second length would be laid, and later read, at positions
modulo the wrong length. (2) A tree's mask length exceeds its length (closeTrees): the positions of
a mask row from 2 ^ logN on would lie in no leaf, so no root would bind the symbols there.
What treesCan checks is stated as a proposition on the messages, and proved in both directions, in
Johnson/Desc/Own/TreesMean.lean (treesCan_iff): no mask rows of two lengths meet in one tree, and
none are longer than their tree's main rows.
HOW FAR THE TEXT IS ITS OWN: NOT FAR. It is the hand-written program's layTrees
(OnBytes/Iop/Ground.lean), taken over under names. The four functions follow layTrees line for line:
its inner function, its two passes, the body of its loop and its last step, each under a name; no
line of the reckoning is new. One constant is written out: 2 ^ 32 - 1 for noId, the number that
names no class. So it adds no second, independent eye.
What else is taken from the hand-written program's files: the records Codes, Code, OracleNotice,
OracleShape, TreeShape and TreeLay with their fields, the default values of Code, OracleNotice and
OracleShape, and two functions that give a number and cannot say no: TreeShape.mainWidth and
TreeShape.maskWidth. No function of these files that says yes or no, or that may give nothing, is
called: a walk by constants beneath treesMade and treesCan finds none.
That treesMade is the program's layTrees (OnBytes/Iop/Ground.lean), and treesCan its «isSome», at
all arguments, is proved beside, in Johnson/Desc/Own/TreesAgree.lean, which no block imports.
LIMIT: whether this is the right way to lay trees is not said here.
No theorem here. Nothing on soundness.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

/-- One pass over the messages: each goes to the first tree that fits it, or opens a new one. The
number that names no class is 2 ^ 32 - 1. -/
def treeOfPass (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (s : Array OnBytes.TreeShape × Array Nat × Array Nat) :
    Array OnBytes.TreeShape × Array Nat × Array Nat :=
  (List.range sent.size).foldl (fun s i =>
    let n := sent.getD i default
    if (n.shape.mainRows == 0) != maskOnly then s
    else
      let logN := (codes.base.getD n.shape.code default).logN
      let fits (t : Nat) : Bool :=
        s.2.1.getD t (2 ^ 32 - 1) == n.leafClass && (maskOnly || (s.1.getD t {}).logN == logN)
      match (List.range s.1.size).find? fits with
      | some t => (s.1, s.2.1, s.2.2.setIfInBounds i t)
      | none =>
        (s.1.push (if maskOnly then {} else { logN := logN }), s.2.1.push n.leafClass,
          s.2.2.setIfInBounds i s.1.size)) s

/-- Both passes: first the messages with main rows, then the others. -/
def treeOf (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    Array OnBytes.TreeShape × Array Nat × Array Nat :=
  treeOfPass codes sent true (treeOfPass codes sent false (#[], #[], Array.replicate sent.size 0))

/-- Message number i is laid into its tree; nothing if its mask rows have another length than those
that the tree holds. -/
def fillStep (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (tree : Array Nat)
    (s : Array OnBytes.TreeShape × Array Nat × Array Nat) (i : Nat) :
    Option (Array OnBytes.TreeShape × Array Nat × Array Nat) :=
  let n := sent.getD i default
  let at0 := tree.getD i 0
  let zk := (codes.mask.getD n.shape.maskCode default).logN
  let before := (s.1.getD at0 {}).mainSymbols.size
  if 0 < n.shape.maskRows && 0 < s.2.2.getD at0 0 && (s.1.getD at0 {}).logNzk != zk then none
  else
    some (s.1.modify at0 fun t =>
        { t with
          logNzk := if 0 < n.shape.maskRows then zk else t.logNzk
          mainSymbols := t.mainSymbols.push (n.shape.mainRows * n.shape.mainDeg)
          maskSymbols := t.maskSymbols.push (n.shape.maskRows * 3) },
      s.2.1.push before, s.2.2.modify at0 (· + n.shape.maskRows * 3))

/-- The last step: a tree without main symbols gets its mask rows' length as its length; nothing if
some tree holds mask symbols that are longer than the tree. -/
def closeTrees (tree : Array Nat) (filled : Array OnBytes.TreeShape × Array Nat × Array Nat) :
    Option OnBytes.TreeLay :=
  let shapes := filled.1.map fun t => if t.mainWidth == 0 then { t with logN := t.logNzk } else t
  if shapes.all fun t => t.maskWidth == 0 || t.logNzk ≤ t.logN then
    some { tree := tree, part := filled.2.1, shapes := shapes }
  else none

/-- The oracle messages of one prover's message, placed in trees. -/
def treesMade (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    Option OnBytes.TreeLay :=
  match (List.range sent.size).foldlM (fillStep codes sent (treeOf codes sent).2.2)
      ((treeOf codes sent).1, #[], Array.replicate (treeOf codes sent).1.size 0) with
  | none => none
  | some filled => closeTrees (treeOf codes sent).2.2 filled

/-- The trees can be laid. -/
def treesCan (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) : Bool :=
  (treesMade codes sent).isSome

end VerifiableInference.Desc.Own
