-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ChainRule.lean: the rule of composition for ONE HASH CHAIN of a proof file,
stated of the verifier's own decision. A SHEET OF STATEMENTS: definitions, and propositions written
as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

The setting. A proof file holds three hash chains. Each chain is one public-coin interaction made
non-interactive: a list of rounds, in each of which the prover sends a message (field elements,
roots of Merkle trees) and the verifier's challenge is read off a hash of all that went before. The
description of the protocol (Johnson/Desc/Block.lean) writes a chain as a list of BLOCKS. A block
states its rounds and has a verifier with code: from a record that the verifier carries from block
to block, the block's own rounds, and the opened leaves that the block is owed, to the next record
or a refusal. The chain's decision is the fold of these verifiers over the chain's rounds: `chainAt
name ft bs`.

Words. A TREE is a Merkle tree, that is, an oracle message; a COLUMN is the symbol at one of its
leaves. A chain's WRITTEN ROUNDS are its rounds as the file format has them (their data: `RDT`,
OnBytes/Maker/Trees.lean): the challenge of such a round is blocks of a hash's output, with bits of
proof of work among them. A STRETCH is the run of consecutive written rounds that belongs to one
block. A BOUNDARY lies between two blocks that follow each other, in front of the first, or behind
the last. A STATEMENT AT A BOUNDARY is the carried record together with the oracles that exist
there. A PIECE is a block together with the data of its stretch.

What is said. The library has (a) a stretch of written rounds as an interactive oracle reduction
that takes trees over and leaves trees, for any decision on what the verifier is shown of the
stretch (`stageIOR`, OnBytes/Maker/Stage.lean); (b) a bare block between two joints, and its
property (`KObj.BK`, `BK.Good`, Johnson/E/KObj/Blocks.lean: round-by-round knowledge soundness at a
list of errors with a named extractor, into the next joint's condition; locality); (c) the rule that
two good blocks one after the other are one good block (`BK.good_seq`). Here (1) each block of the
description, at its own stretch, IS such a bare block (`Piece.bk`): its decision is the chain's fold
at the list of this one block, no other text; (2) the chain's decision, at the chain's whole list of
rounds, IS such a reduction (`chainIOR`); (3) `ChainRule`: if every block is good between its two
boundaries, AND THE STRETCHES TILE THE CHAIN (`Tiled`: they cover its rounds and its opened leaves,
each once, in order), the chain's decision is knowledge sound from the first boundary to the last,
at the blocks' errors, appended.

Main names.
  `Frame`, `Frame.E`, `jointAt`: what is fixed for one chain; the oracles at a boundary (one type at
    all boundaries); what stands at a boundary.
  `Piece`; `foldRun`, `Piece.stage`, `Piece.run`, `Piece.ior`, `Piece.bk`: a block at its stretch,
    as a reduction and as a bare block.
  `rowIOR`, `rowExt`, `rowErr`: the blocks one after the other, by the library's `IOR.seq`,
    `IOR.extSeq`, `Err.app`. `chainIOR`, `foldRed`: the chain's decision at the chain's whole list
    of rounds.
  `EachGood`: one premise for each block. `Piece.Owed`, `Piece.Listed`, `Tiled`: the stretches tile
    the chain.
  THE STATEMENTS: `RowRule` · `ShapeIsChain` · `FoldIsRow` · `ChainRule` · `ChainRuleAt` (at
    `Chain.blocksInOrder c`) · `PieceOfProved`, `PieceGood` (one law for each kind of block, and from it the
    premise that `EachGood` asks) · `RunsReach` (with `runAt`, `recordAt`: each named run of claims
    of a link reaches the batching) · `FoldBelow` (with `foldRunW`, `below`: the test that every
    word is below the prime).
  FORMS OF PREMISES FOR A LINK: `ClaimsHold`, `BatchKnows`, `ClaimsSay`: definitions, no statement.

One shape of premise for two sorts of block. Some blocks test equations; some only hear: they take
messages and challenges into the record and test nothing (the rounds of a lookup argument are such),
and make claims of what they heard, which a later block of the same link tests. `EachGood` has ONE
shape for both. A block that only hears says yes at every stretch of the right form, and the content
of its `BK.Good` lies in the relation behind it, which is to say that its claims hold
(`ClaimsHold`); `ClaimsSay` ties these claims to the proved reduction's out-statement, and
`BatchKnows` is where they are tested.

Kin that is called, not typed anew: two stretches behind each other (`Fo.Peel.toJoin`, `rvT_app`,
`passT_app`, `rvT_length`, OnBytes/Tie/Pv/Lookup/Peel/FoPeelJoinT.lean; `uLT_append`,
OnBytes/Flat/ShapesRow.lean); `stageIOR_isLocal` (OnBytes/Maker/RowLaws.lean); the three chains in a
row (`rowOf`, OnBytes/Maker/Row.lean; `rowOf_of_whole`, RowWhole.lean); `know_carryS`
(OnBytes/Flat/CarrySkip.lean).

Limits. (1) NOTHING ON ACCEPTANCE: every statement here bounds what a cheating prover can reach;
none says that an honest prover is accepted. (2) DEGENERATE CASES: each of these makes `ChainRule`'s
premises or its conclusion true and empty: an error that is the number of a round's challenges
(nothing here forbids it: the errors' size is the reader's to look at) · a condition `on` that holds
of no statement · a last relation that holds of no witness, with a last condition that holds of all
· blocks that refuse all · a type W without a member · AN EXTRACTOR BY CHOICE: `ext` is any
function, and Lean models no running time: with an extractor that picks a witness by choice,
knowledge soundness says no more than soundness (Ior/Know.lean says so of the notion itself): that
an extractor is one that can be run is the reader's to look at · pieces whose data are not the
file's: ds is a parameter, tied to the block's declared rounds by `Owed`'s two counts alone, and to
the file's data by nothing here. A chain without a block cannot be written here (a row has a first
piece; `chainAt` refuses an empty list). A block without a round is a piece without a written round:
it has its position in the row, and no error to pay (an example at the file's end). (3) EACH BLOCK
COUNTS ONCE: a row is a list, and `ChainRuleAt` asks that its blocks, in order, are the chain's list
of blocks. That no run of claims is forgotten or named twice inside a link is a test of Block.lean's
(`orderOk`), not asked here. (4) One type W of witnesses stands at all boundaries: it is meant to be
met by a record of all that is ever witnessed along the chain (what the stored table commits to;
each sent message's decoding), of which a boundary's relation reads its part. (5) `ChainRule`
concludes knowledge soundness of a reduction alone: that the oracles are strings read by position,
and that the verdict is local, which `RowRule` still has in hand, are let go. The name of the chain
is idle (it stands in a refusal's words alone), and so is the type of claims outside section 6.
Nothing is said of several requests that share a chain, of three chains, of a key file, of
`FileDescription` or `runEnd`, of `planOk`. (6) An error counts values of a written round's challenge as it
is drawn. `foldRun` does not ask that the words shown are below the field's prime, as the file's
decision does in front of its folds: so in `ChainRule` as it is typed a block has to be good also at
transcripts with a word that is not; section 7 has the way round. (7) `Owed`, `Listed` and `Tiled`
are premises; a tree's number is its number through the whole file, so a tree that is taken over
from an earlier chain has a smaller number than every `base` and passes `Listed`'s second clause.
That a block's declared rounds ask for just the columns that the data of its stretch give is a law
of the format's, stated elsewhere. (8) That a relation at a boundary says what the protocol means
there is each block's matter: on and R are parameters. (9) The link's lemma is not stated as a
consequence of anything here. (10) No rule is here for a block that is typed at a part of the record
and lifted (`Block.lift`).

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import OnBytes.Maker.Stage
import OnBytes.Flat.CarrySkip
import Johnson.E.KObj.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-! ## 1 A statement at a boundary -/

/-- What is fixed for one hash chain before any of its rounds. -/
structure Frame where
  /-- the depth of the stored table: a Merkle tree that was committed to before the proof, of which
  the verifier reads leaves -/
  a : ℕ
  /-- every Merkle tree that this chain can open or sends itself, each with its number (trees are
  numbered through the whole file, in the order of sending) and its depth -/
  all : List LeftT
  /-- under which key the opened leaves of the tree with a given number stand in what this chain's
  verifier is shown -/
  key : ℕ → ℕ
  /-- a number of the file format that `Block.step` takes: the number in the label of the first tree
  that the chain sends itself -/
  ft : ℕ

/-- The oracles that exist between two blocks: the stored table and all the trees of `F.all`. It is
one type at all boundaries of the chain: a tree that is not yet sent holds empty columns. -/
abbrev Frame.E (F : Frame) : ExtSpec := (oneExternalString (2 ^ F.a) SgX).prod (EjOf F.all)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- What stands between two blocks, in the library's form (`KObj.JK`, a joint): a statement there is
a pair of the record that the verifier carries and the oracles; W is the type of witnesses; `on` is
the condition on the statements of which soundness speaks; R is the relation between a statement and
a witness that is claimed there. -/
abbrev jointAt (F : Frame) (S W : Type) (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop) :
    JK :=
  ⟨S, F.E, W, on, R⟩

/-! ## 2 A block at its stretch, as a bare block of the library -/

/-- A block of the description together with its stretch: the consecutive rounds of the chain that
belong to it. -/
structure Piece (C : CK) (F : Frame) (S Cl W : Type) where
  b : Block S Cl
  /-- the number, through the whole file, of the first tree that is sent in the stretch -/
  base : ℕ
  /-- the data of the stretch's rounds as the file format has them: for each round what the message
  holds, what is drawn, which trees are sent and which are opened -/
  ds : List RDT
  /-- rounds that are shown to the verifier behind the stretch's own although no transcript holds
  them: none, but for the empty round that closes the first chain -/
  back : List Fmt.RoundView := []
  /-- the extractor: from the statement in front of the block, the stretch's transcript and a
  witness of the statement behind the block, to a witness of the statement in front -/
  ext : S × F.E.Str → Iop.Tr (uLT C ds) → W → W
  /-- the block's own errors: for each of its rounds, how many values of the challenge may lead a
  prover that has lost to a position in which it has not -/
  err : Err (uLT C ds)

/-- The stretch in the library's form (`StageD`): all trees of the frame are at hand in front of it,
and all are left behind it. -/
abbrev Piece.stage (p : Piece C F S Cl W) : StageD := ⟨F.a, p.base, F.all, p.ds, F.key, F.all⟩

/-- **The chain's decision itself**: `chainAt name ft bs`, the fold of the blocks'
verifiers (Johnson/Desc/Block.lean), as a function from the carried record and what the verifier is
shown (the rounds and the opened leaves) to the last record, or to nothing where any block refuses,
a round or an opened leaf is left over, or the list of blocks is empty. `back`: rounds that are put
behind those shown. The words of a refusal are dropped. -/
def foldRun (F : Frame) (name : String) (bs : List (Block S Cl)) (back : List Fmt.RoundView) :
    S → Fmt.View → Option S := fun s v =>
  (chainAt name F.ft bs s ⟨v.rounds ++ back, v.opened⟩).toOption

/-- One block's decision on its own stretch: THE SAME FOLD, at the list that holds this one block.
So it asks what the chain's decision asks: the stretch has just the rounds that the block declares,
`Block.step` says yes, and no opened leaf is left over. There is no second text of any verifier in
this file. -/
def Piece.run (p : Piece C F S Cl W) : S → Fmt.View → Option S := foldRun F p.b.name [p.b] p.back

/-- **The block as an interactive oracle reduction** over its own rounds, by the library's
`stageIOR`: from a statement in front of the block to the statement behind it, or a refusal.
`stageIOR` makes what the verifier is shown out of the transcript and the oracles, and tests in
front of the decision that the proofs of work pass, that no part of a round's draws is shortened,
and that a leaf read of the stored table carries its own position. -/
abbrev Piece.ior (p : Piece C F S Cl W) : IOR S F.E S F.E := stageIOR C p.stage p.run

/-- The same with its extractor and its errors: a bare block of the library (`KObj.BK`) between what
stands in front of it (on, R) and what stands behind it (on', R'). -/
abbrev Piece.bk (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) : BK (jointAt F S W on R) (jointAt F S W on' R') :=
  ⟨p.ior, p.ext, p.err⟩

/-- How many trees are sent in the stretch. -/
def Piece.trees (p : Piece C F S Cl W) : ℕ := (p.ds.map (·.trees.length)).sum

/-- **The block is owed just its stretch.** The stretch has as many rounds as the block declares;
and, whatever the oracles and the transcript are, the stretch's draws open just as many leaves as
the block's declared rounds say that it reads. It ties the block's declaration to the data of its
stretch by these two counts. -/
def Piece.Owed (p : Piece C F S Cl W) : Prop :=
  p.ds.length + p.back.length = p.b.rounds.length ∧
    ∀ (y : F.E.Str) (τ : Iop.Tr (uLT C p.ds)),
      ((p.b.reads F.ft (((sView C p.stage y τ).rounds ++ p.back).map (·.drawn))).flatMap id).length
        = (sView C p.stage y τ).opened.length

/-! ## 3 The blocks one after the other, and the chain's decision -/

/-- The blocks' reductions one after the other, by the library's sequential composition. -/
def rowIOR : Piece C F S Cl W → List (Piece C F S Cl W) → IOR S F.E S F.E
  | p, [] => p.ior
  | p, q :: l => p.ior.seq (rowIOR q l)

/-- Their errors, one list behind the other. -/
def rowErr : (p : Piece C F S Cl W) → (l : List (Piece C F S Cl W)) → Err (rowIOR p l).shape
  | p, [] => p.err
  | p, q :: l => Err.app p.err (rowErr q l)

/-- Their extractors composed, the last block's first. d: the value where a block refuses. -/
def rowExt (d : W) : (p : Piece C F S Cl W) → (l : List (Piece C F S Cl W)) →
    S × F.E.Str → Iop.Tr (rowIOR p l).shape → W → W
  | p, [] => p.ext
  | p, q :: l => IOR.extSeq p.ior (rowIOR q l) p.ext (rowExt d q l) d

/-- **The chain's decision as an interactive oracle reduction** over the chain's own rounds:
`stageIOR` at the data of all the rounds, with `foldRun` at the whole list of blocks as the
decision. -/
abbrev chainIOR (C : CK) (F : Frame) (name : String) (bs : List (Block S Cl)) (base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView) : IOR S F.E S F.E :=
  stageIOR C ⟨F.a, base, F.all, ds, F.key, F.all⟩ (foldRun F name bs back)

/-- The data of all the rounds: the stretches' data, appended. -/
def rowData (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) : List RDT :=
  (p :: l).flatMap (·.ds)

/-- The rounds that the last block has put behind its own. -/
def rowBack (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) : List Fmt.RoundView :=
  ((p :: l).getLast (List.cons_ne_nil p l)).back

/-- `chainIOR` as a reduction whose list of rounds is written as the stretches' lists appended. That
list equals the chain's own by the equation h (`ShapeIsChain`), not by definition: so a transcript
is carried along h. -/
def foldRed (name : String) (bs : List (Block S Cl)) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l)) :
    Reduction (S × F.E.Str) (S × F.E.Str) where
  shape := (rowIOR p l).shape
  out := fun a τ =>
    (chainIOR C F name bs p.base (rowData p l) (rowBack p l)).red.out a
      (cast (congrArg Iop.Tr h) τ : Iop.Tr (uLT C (rowData p l)))

/-! ## 4 The premises and the rule -/

/-- **One premise for each block.** Boundary i lies in front of the i-th block; `on i` and `R i` are
the condition and the relation there. The premise: each block, as a bare block between boundary i
and boundary i + 1, has the library's property `BK.Good`, which is three things: every oracle of its
rounds is a string that is read by position; its verdict and the oracles that it leaves depend on
the oracles only at the positions that it declares to read; and it is round-by-round knowledge
sound, at its own errors and with its own extractor, from R i to R (i + 1), where reaching a
statement outside `on (i + 1)` counts as the prover's win. The first two hold of every stretch (see
`PieceGood`). The condition behind a block is a promise on which the later blocks' clauses rest. A
block that can leave its promise, and past which a further claim is carried, owes more than the
third part: `Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean). The condition and the relation are
given by the boundary's number alone: which statement is claimed at a boundary does not depend on
what the prover has sent. -/
def EachGood (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l => (p.bk (on i) (on (i + 1)) (R i) (R (i + 1))).Good ∧ EachGood on R (i + 1) l

/-- The trees that are sent in the stretch stand in the frame's list, each once, under its number
and at its depth; and no round of the stretch opens a tree that is sent only behind the stretch. -/
def Piece.Listed (p : Piece C F S Cl W) : Prop :=
  (∀ n sh, treeShT p.ds n = some sh → (F.all.filter (·.no == p.base + n)).map (·.a) = [sh.a]) ∧
    ∀ d ∈ p.ds, ∀ j ∈ d.opens, j < p.base + p.trees

/-- **The stretches tile the chain.** Each block is owed just its stretch (`Owed`); its trees are
listed (`Listed`); the trees of the stretches are numbered one stretch after the other; and only the
last block has rounds put behind its own. -/
def Tiled : Piece C F S Cl W → List (Piece C F S Cl W) → Prop
  | p, [] => p.Owed ∧ p.Listed
  | p, q :: l => p.Owed ∧ p.Listed ∧ p.back = [] ∧ q.base = p.base + p.trees ∧ Tiled q l

/-- If each block is good, the blocks one after the other are one good bare block, from the first
boundary to the last, at the blocks' errors, appended. (The library's rule for two blocks, along a
list.) -/
def RowRule : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (i : ℕ) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)),
    EachGood on R i (p :: l) →
    (⟨rowIOR p l, rowExt d p l, rowErr p l⟩ :
      BK (jointAt F S W (on i) (R i))
        (jointAt F S W (on (i + 1 + l.length)) (R (i + 1 + l.length)))).Good

/-- The stretches' lists of rounds, appended, are the chain's list of rounds. -/
def ShapeIsChain : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)),
    (rowIOR p l).shape = uLT C (rowData p l)

/-- **The chain's decision is the blocks' decisions one after the other.** Where the stretches tile
the chain: at every statement and every transcript the chain's decision, made on what the verifier
is shown of the whole chain, and the blocks' reductions composed, each made on what it is shown of
its own stretch and of the oracles left by the blocks before it, give the same: both refuse, or both
return the same record and leave the same oracles. AN EQUATION OF THE WHOLE VERDICT, not an
implication: so the fold drops no block's verdict and adds none. -/
def FoldIsRow : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l)),
    Tiled p l →
    ∀ (a : S × F.E.Str) (τ : Iop.Tr (rowIOR p l).shape),
      (foldRed name ((p :: l).map (·.b)) p l h).out a τ = (rowIOR p l).red.out a τ

/-- **The rule of composition for one chain, of the chain's own decision.** If the stretches tile
the chain and each block is good between its two boundaries, then the chain's decision is
round-by-round knowledge sound from the relation at the first boundary to the relation at the last
(a last statement outside the last condition counts as the prover's win), with the blocks'
extractors composed and at the blocks' errors, appended. -/
def ChainRule : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l)),
    Tiled p l → EachGood on R 0 (p :: l) →
    (foldRed name ((p :: l).map (·.b)) p l h).KnowInto (on 0) (on (1 + l.length)) (R 0)
      (R (1 + l.length)) (rowExt d p l) (rowErr p l)

/-- The same for a chain as the description writes it: blocks in front, links, blocks behind
(`Chain.blocksInOrder`). The first premise: the pieces' blocks, in order, ARE the chain's list of blocks: so
each block of the chain has just one piece. -/
def ChainRuleAt : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (c : Chain S Cl) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l)),
    (p :: l).map (·.b) = c.blocksInOrder → Tiled p l → EachGood on R 0 (p :: l) →
    (foldRed name c.blocksInOrder p l h).KnowInto (on 0) (on (1 + l.length)) (R 0) (R (1 + l.length))
      (rowExt d p l) (rowErr p l)

/-! ## 5 One law for each kind of block -/

/-- **One law for each kind of block: from a proved reduction to the block.** Kp is a reduction of
the library that is proved knowledge sound; its rounds are typed (field elements are drawn), while
the block's rounds are as the file has them (blocks of a hash's output are drawn). G reads the
block's transcript as one of Kp; rd reads the statement in front of the block as a statement of Kp.
The first premise: the block's errors bear Kp's along G. The third premise, asked at every statement
with `on` and AT EVERY TRANSCRIPT, so at all that the verifier can ever be shown: WHERE THE BLOCK
SAYS YES, Kp SAYS YES AT THE SAME TRANSCRIPT, READ BY G; what Kp puts out has a witness wherever the
statement behind the block has one; and from Kp's extracted witness the block's extractor's value is
a witness in front. Then the block's own reduction is knowledge sound. The witness w' of what Kp
puts out is only asked to exist: it stands in no extractor: the block's extractor is the piece's own
field `ext`; whoever makes `ext` out of Kp's extractor needs w' as a named function of the statement
behind and its witness. This is the library's `know_carryS` (OnBytes/Flat/CarrySkip.lean) at the
block's own reduction. -/
def PieceOfProved : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (Xp Yp Wp Wq : Type)
    (Kp : Reduction Xp Yp) (G : S × F.E.Str → CarryS (uLT C p.ds) Kp.shape) (δ : Err Kp.shape)
    (rd : S × F.E.Str → Xp) (on : S × F.E.Str → Prop) (onp : Xp → Prop)
    (RA RB : S × F.E.Str → W → Prop) (RAp : Xp → Wp → Prop) (RBp : Yp → Wq → Prop)
    (ep : Xp → Iop.Tr Kp.shape → Wq → Wp),
    (∀ a, (G a).Fits δ p.err) → (∀ a, on a → onp (rd a)) →
    (∀ a τ a' w, on a → p.ior.red.out a τ = some a' → RB a' w →
      ∃ τ' y w', (G a).tr τ = some τ' ∧ Kp.out (rd a) τ' = some y ∧ RBp y w' ∧
        (RAp (rd a) (ep (rd a) τ' w') → RA a (p.ext a τ w))) →
    Kp.Know onp RAp RBp ep δ →
    p.ior.red.Know on RA RB p.ext p.err

/-- **From the same premises to the premise that `EachGood` asks.** `BK.Good` is three things: every
oracle of the block's rounds is a string that is read by position; the verdict and the oracles left
depend on the oracles only at the positions that are declared as read; and knowledge soundness INTO
the next boundary's condition. The first two hold of every stretch (`pointsT`,
OnBytes/Maker/TreesLaws.lean; `stageIOR_isLocal`, OnBytes/Maker/RowLaws.lean). For the third there
is one premise more than in `PieceOfProved`: the block carries the condition on: from a statement
with `on` it puts out statements with `on'` alone. -/
def PieceGood : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (Xp Yp Wp Wq : Type)
    (Kp : Reduction Xp Yp) (G : S × F.E.Str → CarryS (uLT C p.ds) Kp.shape) (δ : Err Kp.shape)
    (rd : S × F.E.Str → Xp) (on on' : S × F.E.Str → Prop) (onp : Xp → Prop)
    (RA RB : S × F.E.Str → W → Prop) (RAp : Xp → Wp → Prop) (RBp : Yp → Wq → Prop)
    (ep : Xp → Iop.Tr Kp.shape → Wq → Wp),
    (∀ a, (G a).Fits δ p.err) → (∀ a, on a → onp (rd a)) →
    (∀ a τ a' w, on a → p.ior.red.out a τ = some a' → RB a' w →
      ∃ τ' y w', (G a).tr τ = some τ' ∧ Kp.out (rd a) τ' = some y ∧ RBp y w' ∧
        (RAp (rd a) (ep (rd a) τ' w') → RA a (p.ext a τ w))) →
    (∀ a τ a', p.ior.red.out a τ = some a' → on a → on' a') →
    Kp.Know onp RAp RBp ep δ →
    (p.bk on on' RA RB).Good

/-! ## 6 Forms of premises for a link -/

/-- Inside a link of a chain, blocks make CLAIMS (for us: linear forms in hidden values that are
said to be 0), which one later block, the batching, tests all at once under a random combination.
`run` is a named run of claims of a block: from the carried record to a list of claims, or a
refusal. This proposition: THE RUN RETURNS, and every claim that it makes of the record holds.
`Holds`: what a claim says of a statement and a witness; it is a parameter here. -/
def ClaimsHold (Holds : Cl → S × F.E.Str → W → Prop) (run : S → Except String (List Cl × S))
    (a : S × F.E.Str) (w : W) : Prop :=
  ∃ cls s', run a.1 = .ok (cls, s') ∧ ∀ c ∈ cls, Holds c a w

/-- THE LINK'S OWN LEMMA, AS A PREMISE. The batching's block is handed all the link's claims as one
function (`claimsIn K.hear K.order`: every named run of every earlier block of the link, in the
link's order). The premise: pb is the piece that holds that block; and it is good from the relation
"all these runs return, all their claims hold, and Rest" to the relation behind it. So whoever
proves it has to show that where the batching says yes the claims were made: a batching that does
not call what it is handed does not meet it. -/
def BatchKnows (K : Link S Cl) (pb : Piece C F S Cl W) (Holds : Cl → S × F.E.Str → W → Prop)
    (on on' : S × F.E.Str → Prop) (Rest Behind : S × F.E.Str → W → Prop) : Prop :=
  pb.b = K.batch (claimsIn K.hear K.order) ∧
    (pb.bk on on' (fun a w => ClaimsHold Holds (claimsIn K.hear K.order) a w ∧ Rest a w)
      Behind).Good

/-- THE LAW OF A BLOCK THAT ONLY HEARS. Some blocks test no equation: they take the prover's
messages and the challenges into the record, and make claims of them later. For such a block the
sentence "where the block says yes, the proved reduction says yes" is empty. Its law is on its
claims: where its run returns and the claims that it makes of what was heard hold, the out-statement
of the proved reduction holds. `Says`: that out-statement, read at the boundary behind the block. -/
def ClaimsSay (Holds : Cl → S × F.E.Str → W → Prop) (run : S → Except String (List Cl × S))
    (Says : S × F.E.Str → W → Prop) : Prop :=
  ∀ a w, ClaimsHold Holds run a w → Says a w

/-- The run of claims that stands at the number k of a link's order (from 0), if there is one. -/
def runAt (K : Link S Cl) (k : ℕ) : Option (ℕ → S → Except String (List Cl × S)) :=
  (K.order[k]?).bind fun o => (K.hear[o.1]?).bind fun b => b.claims.lookup o.2

/-- The record at which a link's order calls its run number k: the record behind the runs that the
order calls earlier, from the record s in front of the batching; nothing where one of these refuses.
-/
def recordAt (K : Link S Cl) (k : ℕ) (s : S) : Option S :=
  (claimsIn K.hear (K.order.take k) s).toOption.map (·.2)

/-- The number of claims that the runs which the order calls earlier have made: what the run number
k is handed beside the record (Block.lean). The same fold as `recordAt`. -/
def sofarAt (K : Link S Cl) (k : ℕ) (s : S) : Option ℕ :=
  (claimsIn K.hear (K.order.take k) s).toOption.map (·.1.length)

/-- **Each named run reaches the batching.** Where all the runs of a link's order return and all
their claims hold at the boundary in front of the batching, the run number k is there, the runs in
front of it return, and it returns, and its claims hold, at the record at which the order calls it.
The premise: what a claim says does not change with the carried record: it reads the oracles and the
witness (a run may change the record: it may lay a mark in it). -/
def RunsReach : Prop :=
  ∀ (S Cl W : Type) (F : Frame) (K : Link S Cl) (Holds : Cl → S × F.E.Str → W → Prop),
    (∀ c s s' y w, Holds c (s, y) w → Holds c (s', y) w) →
    ∀ k, k < K.order.length → ∀ (a : S × F.E.Str) (w : W),
      ClaimsHold Holds (claimsIn K.hear K.order) a w →
      ∃ run s n, runAt K k = some run ∧ recordAt K k a.1 = some s ∧ sofarAt K k a.1 = some n ∧
        ClaimsHold Holds (run n) (s, a.2) w

/-! ## 7 The test that every word is below the prime -/

/-- A file's decision asks in front of its three folds that every word which is shown as part of a
field's element is below the field's prime (`viewWordsBelowPrime`, Johnson/Desc/Block.lean). `foldRun` does not
ask it. This is the chain's decision with that test in front. -/
def foldRunW (F : Frame) (name : String) (bs : List (Block S Cl)) (back : List Fmt.RoundView) :
    S → Fmt.View → Option S := fun s v =>
  if viewWordsBelowPrime v then foldRun F name bs back s v else none

/-- A DEVICE OF THE PROOF: it is no text of the description and runs nowhere. The block that first
makes the same test of its own rounds and of the opened leaves that it is handed, and then decides
as b does. -/
def below (b : Block S Cl) : Block S Cl :=
  { b with
    decide := fun s rs gs =>
      if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime" }

/-- **The test in front of the fold is the blocks' own tests.** The fold of the blocks `below b` is
the fold of the blocks b with `viewWordsBelowPrime` in front: an equation of the whole verdict. The text that
runs is the right-hand side: the test on all that is shown, once, then the fold. What it is for:
`ChainRule`, read at pieces that hold the blocks `below b`, is the rule of composition for the
decision with that test in front; and what is then owed for a block b is that `below b` is good: b
has to be sound only at transcripts whose words are below the prime, since at the others `below b`
refuses. -/
def FoldBelow : Prop :=
  ∀ (S Cl : Type) (F : Frame) (name : String) (bs : List (Block S Cl)) (back : List Fmt.RoundView),
    viewWordsBelowPrime ⟨back, []⟩ = true →
    foldRun F name (bs.map below) back = foldRunW F name bs back

/-! ## 8 Do the statements elaborate where they are meant? -/

-- a block of the description goes in as it is, at any type of carried records and of claims
example (S Cl W : Type) (C : CK) (F : Frame) (b : Block S Cl) (base : ℕ) (ds : List RDT)
    (e : S × F.E.Str → Iop.Tr (uLT C ds) → W → W) (ε : Err (uLT C ds)) : IOR S F.E S F.E :=
  (⟨b, base, ds, [], e, ε⟩ : Piece C F S Cl W).ior

-- a block without a round (a link's "laid" and "cleared") is a piece without a written round: its
-- reduction has no round and its list of errors is empty. ITS GOODNESS ASKS, with nothing to pay:
-- at every statement a with the front joint's condition: where the record's change f returns, and
-- the statement behind is outside the next joint's condition or w is a witness of it, the
-- extractor's value at (a, w) is a witness of a. The trees sent before pass through unturned.
example (S Cl W : Type) (C : CK) (F : Frame) (f : S → Except String S) (base : ℕ)
    (e : S × F.E.Str → Iop.Tr (uLT C []) → W → W) : IOR S F.E S F.E :=
  (⟨roundlessBlock "laid" 1 (some 0) 0 f, base, [], [], e, ()⟩ : Piece C F S Cl W).ior

-- the conclusion has the form that a rule across the three chains asks of its first reduction
-- (`Know`; at a last condition that holds of all statements `KnowInto` is `Know`:
-- `know_of_knowInto`, Ior/KnowColl.lean)
example (S Cl W : Type) (C : CK) (F : Frame) (name : String) (c : Chain S Cl)
    (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (h : (rowIOR p l).shape = uLT C (rowData p l)) (on₀ : S × F.E.Str → Prop)
    (R₀ R₁ : S × F.E.Str → W → Prop) (d : W) : Prop :=
  (foldRed name c.blocksInOrder p l h).Know on₀ R₀ R₁ (rowExt d p l) (rowErr p l)


end VerifiableInference.Desc.Sound
