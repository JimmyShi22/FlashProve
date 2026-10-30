-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/OwnFold.lean: a fold of the proximity test whose own first message brings
the fresh mask table: the names for stating that the description's fold accepts there. The
verifier's text has two cases (`foldD`, Johnson/Desc/First/Close/Closing.lean): the number of the
fresh table's oracle message is handed in; or nothing is handed in: then the root comes in the
message of the round "FOLD epsilon", and the oracle message is entered on the spot.
Johnson/Prover/Link/FormFold.lean has the names for the first case; here are those for the second.
Definitions alone.

What is proved of them: Johnson/Desc/K12/Honest/OwnFoldLaws.lean.

Main names.
  `rootEntry name items e`   a test on an entry of the plan: in its round one root and "items"
      elements are sent, and one element is sampled; it counts no rows.
  `foldCutOwn k cut`   a test on the declared rounds that are dealt to such a fold: "FOLD epsilon"
      (a root, one element), then k times "FOLD round" (two elements); none opens a tree or a
      stored table. `foldCutsOwn`: this test at the first stage's fold, `foldCut` at every later
      one.
  `ownShape`, `ownLay`, `ownTree`   how the one announced table is placed: alone, in a tree of its
      own; that tree as the book of trees gets it.
  `withOwn S F`, `ownBook`   the statement with the fresh table as its last oracle message; the
      book with the new tree and the new message's place.
  `enteredT p t F`   a structure of this file's making, so that the first case's laws can be
      called: statement, book and count of roots are those that the entering leaves (`recvP_own`,
      OwnFoldLaws.lean); the field `mask` is set here, to the new message's number. No structure in
      a run of the verifier has this form: the entering happens inside `foldD`, and the field
      `mask` is empty in front of such a fold and behind it.
  `FoldFrontOwn p j cur t row L c n`   what is asked in front of such a fold. Each clause is on the
      plan or on the structure in front: none is on a state behind the entering. `frontOwnB`: the
      same as a test with code.
  `foldTOwn`   the structure behind the fold: `foldT` at `enteredT`, with the field `mask` empty,
      as the verifier's text leaves it.

Limits. Names and tests: nothing here says that a structure or a plan meets them.
Of `FoldFrontOwn`: at k = 0 no
structure meets it (`foldShapeFits` asks 1 ≤ k). Nothing on completeness, on soundness or on what is
hidden.
-/
import Johnson.Prover.Link.FormFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link

/-! ## 1 The plan -/

/-- The entry of a round in which one root and "items" elements are sent and one element is sampled;
no rows counted. -/
def rootEntry (name : String) (items : Nat) (e : Fmt.Entry) : Bool :=
  e.name == name && e.drawNZ == 0 && e.count == 1 && e.msg == 24 * items + 32 && e.roots == 1 &&
    e.answers == 0 && e.poss == 0 && e.trits == 0 && e.drawE == 1 && e.rows == 0

/-- The declared rounds of a fold with k row variables that sends its own fresh table. -/
def foldCutOwn (k : Nat) : List Fmt.DeclaredRound → Bool
  | dE :: dR => rootEntry "FOLD epsilon" 1 dE.entry && dR.length == k &&
      dR.all (fun d => elemEntry "FOLD round" 2 d.entry) &&
      (dE :: dR).all fun d => d.stored.isEmpty && d.opens.isEmpty
  | [] => false

/-- The first stage's fold sends its own table; every later stage's table has come earlier. l: the
declared rounds still to be dealt in front of the stage cur (as in `foldCuts`). -/
def foldCutsOwn : Fmt.M1.Stage → List Fmt.M1.Stage → List Fmt.DeclaredRound → Bool
  | _, [], _ => true
  | cur, next :: rest, l =>
    foldCutOwn cur.k (l.take (1 + cur.k)) && foldCuts next rest (l.drop (cur.k + 3))

/-! ## 2 The entering -/

/-- The shape of the tree that holds the fresh table alone: no main symbol; three base-field
elements for each of the 2 ^ h mask rows; both lengths are the mask code's. -/
def ownShape (codes : Codes) (F : FoldShape) : TreeShape :=
  { logN := (codes.mask.getD F.maskCode default).logN
    logNzk := (codes.mask.getD F.maskCode default).logN
    mainSymbols := #[0], maskSymbols := #[2 ^ F.layout.h * 3] }

/-- How the one announced table is placed: part 0 of tree 0 of its prover's message. -/
def ownLay (codes : Codes) (F : FoldShape) : TreeLay :=
  { tree := #[0], part := #[0], shapes := #[ownShape codes F] }

/-- The new tree as the book gets it. firstTree: the number of the first tree that the chain sends.
roots: the roots received before. o: the new oracle message's number. -/
def ownTree (firstTree roots o : Nat) (codes : Codes) (F : FoldShape) : Tree :=
  { shape := ownShape codes F, number := firstTree + roots, src := .own roots, parts := #[o]
    oneList := true }

/-- The statement with the fresh table as its last oracle message. -/
def withOwn (S : Statement) (F : FoldShape) : Statement :=
  { S with oracles := S.oracles.push { shape := (foldMaskNotice F).shape } }

/-- The book with the new tree, and with the new oracle message's place: part 0 of that tree. -/
def ownBook (firstTree : Nat) (S : Statement) (B : TreeBook) (roots : Nat) (F : FoldShape) :
    TreeBook :=
  { trees := B.trees.push (ownTree firstTree roots S.oracles.size S.codes F)
    place := B.place.push (B.trees.size, 0) }

/-- Statement, book and count of roots as the entering of the fold's own table leaves them; the
field `mask` set to the new message's number. Of this file's making, for calling the first case's
laws: no structure in a run of the verifier has this form. -/
def enteredT (p : P12) (t : T12) (F : FoldShape) : T12 :=
  { t with st := withOwn t.st F
           book := ownBook p.nums.firstTree t.st t.book t.roots F
           roots := t.roots + 1
           mask := some t.st.oracles.size }

/-! ## 3 In front of the fold, and behind it -/

/-- **What is asked in front of a fold that sends its own fresh table.** What passes is one claim;
the stage and the next stage's codes are the plan's; no message is named as the mask; statement and
book count the same number of oracle messages; the fold's shape and the row pass the two tests of
Johnson/Desc/Own/Fold.lean that do not read the mask; the new group's two codes are there, and its
mask code is not longer than its main code. -/
structure FoldFrontOwn (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (t : T12) (row : GroupRow)
    (L : GroupLayout) (c : IoppStage) (n : Nat × Nat) : Prop where
  pass : t.pass = .claim row L
  stage : stageAt p j cur = some c
  next : p.idx[j + 1]? = some n
  shape : Own.foldShapeFits t.st (ioppFoldShape c L) = true
  mask : t.mask = none
  inStep : t.st.oracles.size = t.book.place.size
  rowFits : Own.foldRowFits t.st (ioppFoldShape c L) row = true
  group : Ground.ok (Ground.newGroupL t.st n.1 n.2) = true

/-- The same as a test with code: row and layout are read off what passes, the stage and the next
stage's codes off the plan. -/
def frontOwnB (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (t : T12) : Bool :=
  match t.pass, stageAt p j cur, p.idx[j + 1]? with
  | .claim row L, some c, some n =>
    Own.foldShapeFits t.st (ioppFoldShape c L) && t.mask.isNone &&
      t.st.oracles.size == t.book.place.size && Own.foldRowFits t.st (ioppFoldShape c L) row &&
      Ground.ok (Ground.newGroupL t.st n.1 n.2)
  | _, _, _ => false

/-- **The structure behind the fold.** -/
def foldTOwn (p : P12) (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : Nat × Nat)
    (rs : List Fmt.RoundView) : T12 :=
  { foldT (enteredT p t (ioppFoldShape c L)) row L c n t.st.oracles.size rs with mask := none }

end ProofFile.Honest.K12
#print axioms ProofFile.Honest.K12.rootEntry
#print axioms ProofFile.Honest.K12.foldCutOwn
#print axioms ProofFile.Honest.K12.foldCutsOwn
#print axioms ProofFile.Honest.K12.ownShape
#print axioms ProofFile.Honest.K12.ownLay
#print axioms ProofFile.Honest.K12.ownTree
#print axioms ProofFile.Honest.K12.withOwn
#print axioms ProofFile.Honest.K12.ownBook
#print axioms ProofFile.Honest.K12.enteredT
#print axioms ProofFile.Honest.K12.FoldFrontOwn
#print axioms ProofFile.Honest.K12.frontOwnB
#print axioms ProofFile.Honest.K12.foldTOwn
