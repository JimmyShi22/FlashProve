-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedRule.lean: the rule of composition for THE SHARED HASH CHAIN of a proof
file, for the N requests of a batch, stated of the verifier's own decision. A SHEET OF STATEMENTS:
definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

The setting. Johnson/Desc/Sound/ChainRule.lean, whose words are kept here, has a block of the
description at its stretch of a chain's written rounds as a bare block of the library (`Piece.bk`),
the blocks one after the other (`rowIOR`), the chain's decision as a reduction (`foldRed`), and the
rule for ONE statement: if every block is good and the stretches tile the chain, the chain's
decision is knowledge sound round by round. A proof file's second chain is shared: it is run once
for all requests of a batch. A SLOT is here one of the N places of a batch (not, as in the blocks'
own texts, a numbered hidden value of the ledger); each slot that is taken holds a statement of its
own (its own carried record, its own oracles), and all slots see the one transcript of the shared
chain. A round's error then counts the challenges that are bad for SOME slot: N times the error for
one statement, unless the slots have the same bad challenges.

The library says this with keys. A KEY is a function of the statement at a place: what the slots
have in common there. A LINK WITH KEYS is knowledge sound, at one list of errors, for the vectors of
at most N statements that have one key, and takes such vectors, on every transcript, to vectors that
have one key behind it (`LinkJ`, OnBytes/TypedOracleCompiler/Joined/LinkJ.lean; for a bare block `BK.LinkSh`, with
the rule for two in a row `BK.linkSh_seq`, Johnson/TypedOracleCompiler/Joined/LKShared.lean). It is this, not the
clause for one statement, that the rule across a file's three chains asks of the second chain.

What is said. (1) The same pieces, the same row, the same decision as in ChainRule.lean. (2)
`ChainLink`: if every block is such a link, along some keys between, and the stretches tile the
chain, THE CHAIN's DECISION IS ONE, from the first key to the last, AT THE BLOCKS' ERRORS IN A ROW,
EACH ONCE. (3) Where the keys come from, and how a block comes to be such a link from a law for one
statement: its ACTING PART (what it reads of the statement) is in the key; what each slot has of its
own is carried beside.

Main names.
  `BKey F S`: a key at a place: a type and a function of the statement there. `kkAt`: the same as
    the library's key at a joint (`KK`).
  `Keyed N on R i p l kA kZ`: one premise for each block: each is a `BK.LinkSh`, from the key kA to
    the key kZ, along some keys between (the library's `LK.KeyedSh`, over a row of pieces).
  THE RULE: `RowLink` (the blocks one after the other) · `ChainLink` (the chain's decision) ·
    `ChainLinkAt` (at `Chain.blocksInOrder c`).
  `SlotOne`: with one slot or more, the same premises give the clause for one statement: the
    conclusion of `ChainRule`.
  KEYS MADE BACKWARDS: `Piece.keyBack p act kB`: the key in front of a block: its acting part, and
    for each transcript of the block what the key behind it will be, where the block says yes.
    `keysBack`: along a row, from the last key. `AdmBack`: then "one key goes to one key" holds of
    every block.
  A BLOCK's LAW FOR N SLOTS: `Piece.LostBy`: the property towards which the prover has lost is a
    function of the acting part; it holds that the promise behind the block is kept, and that a
    witness behind gives one in front. `PaidOnce`: then the block is a link from the key made
    backwards, at its own errors. `EachLost`, `ChainLinkBack`: the rule with these premises.
  THE LAW THAT IS LEFT AT THE HEAD: `Piece.HandsAct`, `EachHands`: the verdict and the acting part
    behind a block are a function of the acting part in front and the transcript. `HeadOfActs`: then
    the key made backwards is a function of the first acting part. `ChainLinkActs`: THE FORM TO USE:
    the chain's decision is a link from the first acting part to the last.
  FROM ONE STATEMENT TO N: `Piece.RelsBy`, `Piece.ReadsBy`, `LostOfGoodIn`: a block that has
    `GoodIn` (Johnson/Desc/Sound/GoodIn.lean), hands its acting part on, and whose next condition,
    relations and extractor read the statement through the acting part alone, has `LostBy`.
    `LostBeside`: a claim that each slot has of its own and that is carried past the block may be
    laid beside both relations of that law, if the extractor keeps it at outputs inside the promise.
  WHAT IS MEANT: the carried record of the shared chain holds, beside the chain's own part, what was
    handed to the chain; the blocks are typed at the chain's own part and lifted (`Block.lift`).
    `actAt F get lo hi`: the chain's own part of the record, the stored table, and the trees with a
    number from lo to below hi. `LiftHands`: a lifted block whose rounds open no tree with a number
    below lo hands this acting part on. `FoldLift`: the fold of lifted blocks is the fold of the
    blocks, laid back. `hiAt`, `actsOf`, `EachRels`, `EachKeeps`, `ChainLinkOwn`: THE RULE FROM THE
    PREMISE FOR ONE STATEMENT: `EachGoodIn`, `EachRels`, `EachKeeps`, and a test on the data (no
    tree below lo is opened).

Kin that is called, not typed anew: `BK.LinkSh`, `BK.linkSh_seq`, `KK`, `shAn`
(Johnson/TypedOracleCompiler/Joined/LKShared.lean); `BK.LinkB.linkJ` (Johnson/TypedOracleCompiler/Joined/LKLinkJ.lean); `LinkJ`,
`LinkJ.conseq` (OnBytes/TypedOracleCompiler/Joined/LinkJ.lean, LinkJKit.lean); `knowB_of_lost`, `know_of_knowB`
(Ior/BatchSeq.lean); `sameKey_shared`, `slot_shared` (Ior/KnowBRules.lean). For a block without a
round, and for a block whose errors are all 0, two lemmas take `Piece.bk` as it is
[`linkSh_noRound`, `linkSh_zero`, Johnson/TypedOracleCompiler/Joined/TestShared.lean: not in this library; so here
read: not proved in this library]. That `ChainLink`'s conclusion is, as it stands, what the rule
across the three chains asks, is not shown here (Johnson/Desc/Sound/SharedFeeds.lean [not in this
library]).

Limits. (1) NOTHING ON ACCEPTANCE, as in ChainRule.lean. (2) DEGENERATE CASES: each of these makes
the premises or the conclusion true and empty. N = 0: there is no slot, and every reduction is a
link at every list of errors; `SlotOne` is the control that 0 is the only such N. · A KEY IN FRONT
THAT TELLS ALL STATEMENTS APART (the statement itself; a key made backwards over an acting part that
is the whole statement): then the clause speaks of vectors whose slots all hold one statement, and
says no more of a batch than of one request. · An error that is the number of a round's challenges,
or more. · A condition `on` that holds of no statement. · Blocks that refuse all. · A last relation
that holds of no witness, with a last condition that holds of all. · A type S without a member (W
has one: d). · An extractor by choice, and pieces whose data are not the file's (ChainRule.lean,
Limits (2)). (3) ALL THAT SUCH A CLAUSE SAYS HANGS ON WHICH VECTORS HAVE ONE KEY. THAT THE SLOTS OF
A BATCH HAVE ONE KEY AT THE HEAD OF THE SHARED CHAIN IS SHOWN NOWHERE HERE: it is owed where the
first chain's end is known. A key made backwards carries nothing of itself. (4) `LostBy` is a
premise, one for each block. By `LostOfGoodIn` it follows from `GoodIn` and `ReadsBy`. `GoodIn` IS
MORE THAN THE PREMISE OF `ChainRule`: why it is needed where a claim is carried past a block with a
promise, and what is known of its being met, stands in GoodIn.lean. Whether the relations that the
protocol means at the shared chain's places read the statement through `actAt` alone, with the rest
beside them (`LostBeside`), is not looked at here: on and R are parameters. (5) A block is charged
its own field `err`, once. Where the slots' acting parts differ, no rule here makes a shared round
cheaper than N times (the library's `knowB_joining`): then the piece must hold the larger error. (6)
In the annotation `shA` only the shared part of the prover speaks and every challenge is shared:
that the file's second chain is hashed so is the compiler's matter. (7) In `RelsBy` the condition
behind a block is read through the acting part: so a promise that speaks of what each slot has of
its own is not covered. (8) `actAt` holds the chain's own part of the record and the stored table
whole. The table is meant to be common to the slots of a batch, which are requests under one
commitment to the weights; that it is, and that the chain's own first record is, are premises at the
head ((3)). (9) Nothing is said of three chains, of a key file, of `FileDescription` or `runEnd`, of
`planOk`; and `foldRun` does not ask that the words shown are below the field's prime
(ChainRule.lean, Limits (6)).

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodIn
import Johnson.TypedOracleCompiler.Joined.LKLinkJ
import OnBytes.TypedOracleCompiler.Joined.CarryJ
import Ior.KnowBRules

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ shA)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-! ## 1 Keys at the places, and one premise for each block -/

/-- A key at a place: what the statements of one batch have in common there: a type, and a function
of the statement (the carried record with the oracles). -/
abbrev BKey (F : Frame) (S : Type) : Type 1 := Σ κ : Type, (S × F.E.Str → κ)

/-- The same as the library's key at the joint that stands at that place. -/
abbrev kkAt {on : S × F.E.Str → Prop} {R : S × F.E.Str → W → Prop} (k : BKey F S) :
    KK (jointAt F S W on R) :=
  ⟨k.1, k.2⟩

/-- **One premise for each block.** Place i lies in front of the block of the piece p; `on i` and `R
i` are the condition and the relation there, as in `EachGood`. The premise: each block, as a bare
block between its two places, run once by the shared part of the prover under shared challenges, is
a link of a batch of at most N statements (`BK.LinkSh`): it is knowledge sound, at its own errors
and with its own extractor, for the vectors of statements that have one key in front of it, and
takes them on every transcript to vectors that have one key behind it. kA is the key in front of the
row, kZ the key behind it; the keys between are any. -/
def Keyed (N : ℕ) (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) :
    ℕ → Piece C F S Cl W → List (Piece C F S Cl W) → BKey F S → BKey F S → Prop
  | i, p, [], kA, kZ =>
    (p.bk (on i) (on (i + 1)) (R i) (R (i + 1))).LinkSh N (kkAt kA) (kkAt kZ)
  | i, p, q :: l, kA, kZ => ∃ kB : BKey F S,
    (p.bk (on i) (on (i + 1)) (R i) (R (i + 1))).LinkSh N (kkAt kA) (kkAt kB) ∧
      Keyed N on R (i + 1) q l kB kZ

/-! ## 2 The rule -/

/-- The blocks one after the other are one link of the batch, from the first key to the last, at the
errors in a row: the same reduction, extractor and errors as for one statement (`RowRule`). (The
library's rule for two blocks, along a list.) -/
def RowLink : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (i : ℕ) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (kA kZ : BKey F S),
    Keyed N on R i p l kA kZ →
    (⟨rowIOR p l, rowExt d p l, rowErr p l⟩ :
      BK (jointAt F S W (on i) (R i))
        (jointAt F S W (on (i + 1 + l.length)) (R (i + 1 + l.length)))).LinkSh N (kkAt kA)
      (kkAt kZ)

/-- **The rule of composition for the shared chain**, of the chain's own decision: if the stretches
tile the chain and each block is a link of the batch between its two places, then the chain's
decision is a link with keys for the statements of a batch, in rounds in which only the shared part
of the prover speaks: from the relation at the first place to the relation at the last (a last
statement outside the last condition counts as the prover's win), with the blocks' extractors
composed, and at the blocks' errors in a row, each once. -/
def ChainLink : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (kA kZ : BKey F S),
    Tiled p l → Keyed N on R 0 p l kA kZ →
    LinkJ (foldRed name ((p :: l).map (·.b)) p l h) (shA _) N kA.2 kZ.2 (on 0) (R 0)
      (Reduction.orOff (on (1 + l.length)) (R (1 + l.length))) (rowExt d p l) (rowErr p l)

/-- The same at a chain as the description writes it: front, links, back (`Chain.blocksInOrder`). The first
premise: the pieces' blocks, in order, are the chain's list of blocks. -/
def ChainLinkAt : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (c : Chain S Cl) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (kA kZ : BKey F S),
    (p :: l).map (·.b) = c.blocksInOrder → Tiled p l → Keyed N on R 0 p l kA kZ →
    LinkJ (foldRed name c.blocksInOrder p l h) (shA _) N kA.2 kZ.2 (on 0) (R 0)
      (Reduction.orOff (on (1 + l.length)) (R (1 + l.length))) (rowExt d p l) (rowErr p l)

/-- **With one slot or more, the same premises give the clause for one statement**: the conclusion
of `ChainRule`, at the same extractor and errors, whatever the keys are. -/
def SlotOne : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (kA kZ : BKey F S),
    0 < N → Tiled p l → Keyed N on R 0 p l kA kZ →
    (foldRed name ((p :: l).map (·.b)) p l h).KnowInto (on 0) (on (1 + l.length)) (R 0)
      (R (1 + l.length)) (rowExt d p l) (rowErr p l)

/-! ## 3 Keys made backwards -/

/-- **The key in front of a block, made from the key behind it.** `act`: the block's acting part:
what it reads of the statement. The key holds the acting part and, for each transcript of the
block's stretch, what the key behind will be, where the block says yes. (A block can refuse at its
stretch: already the proofs of work are tested in front of its decision.) -/
def Piece.keyBack (p : Piece C F S Cl W) (act kB : BKey F S) : BKey F S :=
  ⟨act.1 × (Iop.Tr (uLT C p.ds) → Option kB.1),
    fun a => (act.2 a, fun τ => (p.ior.red.out a τ).map kB.2)⟩

/-- The keys along a row, made backwards from the last key kZ. `act i`: the acting part at place i.
-/
def keysBack (act : ℕ → BKey F S) (kZ : BKey F S) : ℕ → List (Piece C F S Cl W) → BKey F S
  | _, [] => kZ
  | i, p :: l => p.keyBack (act i) (keysBack act kZ (i + 1) l)

/-- At a key made backwards, vectors with one key go to vectors with one key: of every block,
whatever it does. -/
def AdmBack : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (act kB : BKey F S) (N : ℕ)
    (a : Fin N → Option (S × F.E.Str)), IOR.SameKey (p.keyBack act kB).2 a →
    ∀ τ : BTr N p.ior.shape (shAn p.ior.shape),
      IOR.SameKey kB.2 fun j => (a j).bind fun aj => p.ior.red.out aj (τ.slot j)

/-- **A block's law for N slots.** At the block's errors the prover has lost (`Doomed`: see
`Piece.GoodIn`, Johnson/Desc/Sound/GoodIn.lean) towards a property `lost k` of the transcript that
is a function of the acting part k alone: so slots that have one acting part have the same bad
challenges, and these are paid once. And where `lost k τ` holds and the block says yes, the
statement behind has `on'` (the promise is kept), and every witness of it gives, by the block's
extractor, a witness of the statement in front. It is `GoodIn` with the lost property named and
common to the statements with one acting part. -/
def Piece.LostBy (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) : Prop :=
  ∃ lost : act.1 → Iop.Tr (uLT C p.ds) → Prop,
    (∀ a, on a → Doomed (uLT C p.ds) p.err (lost (act.2 a))) ∧
      ∀ a τ b, on a → lost (act.2 a) τ → p.ior.red.out a τ = some b →
        on' b ∧ ∀ w, R' b w → R a (p.ext a τ w)

/-- A block with that law is a link of the batch, at its own errors, from the key made backwards to
any key behind it. -/
def PaidOnce : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act kB : BKey F S) (N : ℕ),
    p.LostBy on on' R R' act →
    (p.bk on on' R R').LinkSh N (kkAt (p.keyBack act kB)) (kkAt kB)

/-- Every block of a row has that law, at the acting part of the place in front of it. -/
def EachLost (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (act : ℕ → BKey F S) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.LostBy (on i) (on (i + 1)) (R i) (R (i + 1)) (act i) ∧ EachLost on R act (i + 1) l

/-- The rule at keys made backwards: one law for each block; any last key. -/
def ChainLinkBack : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (act : ℕ → BKey F S) (kZ : BKey F S),
    Tiled p l → EachLost on R act 0 (p :: l) →
    LinkJ (foldRed name ((p :: l).map (·.b)) p l h) (shA _) N (keysBack act kZ 0 (p :: l)).2 kZ.2
      (on 0) (R 0) (Reduction.orOff (on (1 + l.length)) (R (1 + l.length))) (rowExt d p l)
      (rowErr p l)

/-! ## 4 The law that is left at the head of the chain -/

/-- The block hands its acting part on: whether it says yes, and the acting part of the statement
behind it, are a function of the acting part in front and the transcript of its stretch. -/
def Piece.HandsAct (p : Piece C F S Cl W) (act act' : BKey F S) : Prop :=
  ∃ G : act.1 → Iop.Tr (uLT C p.ds) → Option act'.1,
    ∀ a τ, (p.ior.red.out a τ).map act'.2 = G (act.2 a) τ

/-- Every block of a row does, from the acting part at the place in front of it to that at the place
behind. -/
def EachHands (act : ℕ → BKey F S) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l => p.HandsAct (act i) (act (i + 1)) ∧ EachHands act (i + 1) l

/-- Then the key that is made backwards from the last acting part is a function of the first acting
part. -/
def HeadOfActs : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (act : ℕ → BKey F S) (i : ℕ)
    (l : List (Piece C F S Cl W)), EachHands act i l →
    ∃ g : (act i).1 → (keysBack act (act (i + l.length)) i l).1,
      ∀ a, (keysBack act (act (i + l.length)) i l).2 a = g ((act i).2 a)

/-- **The rule, in the form to use**: if the stretches tile the chain and every block has its law
for N slots and hands its acting part on, then the chain's decision is a link with keys from the
first acting part to the last, at the blocks' errors in a row, each once. -/
def ChainLinkActs : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (act : ℕ → BKey F S),
    Tiled p l → EachLost on R act 0 (p :: l) → EachHands act 0 (p :: l) →
    LinkJ (foldRed name ((p :: l).map (·.b)) p l h) (shA _) N (act 0).2 (act (1 + l.length)).2
      (on 0) (R 0) (Reduction.orOff (on (1 + l.length)) (R (1 + l.length))) (rowExt d p l)
      (rowErr p l)

/-! ## 5 From the premise for one statement to the law for N slots -/

/-- The condition behind a block, its two relations and its extractor read the statement through the
acting part alone. The condition in front is free: each slot may have its own. -/
structure Piece.RelsBy (p : Piece C F S Cl W) (on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act act' : BKey F S) : Prop where
  cond : ∀ b b', act'.2 b = act'.2 b' → on' b → on' b'
  front : ∀ a a' w, act.2 a = act.2 a' → R a w → R a' w
  behind : ∀ b b' w, act'.2 b = act'.2 b' → R' b w → R' b' w
  ext : ∀ a a' τ w, act.2 a = act.2 a' → p.ext a τ w = p.ext a' τ w

/-- So does the block itself: it hands the acting part on. -/
structure Piece.ReadsBy (p : Piece C F S Cl W) (on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act act' : BKey F S) : Prop where
  hands : p.HandsAct act act'
  rels : p.RelsBy on' R R' act act'

/-- A block that has `GoodIn` for one statement and reads the statement through the acting part
alone has the law for N slots. -/
def LostOfGoodIn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act act' : BKey F S),
    p.GoodIn on on' R R' → p.ReadsBy on' R R' act act' → p.LostBy on on' R R' act

/-- **What each slot has of its own.** Rc: a claim that is carried past the block. The premise on
the extractor, asked at outputs inside the promise alone: where the block says yes, a witness of Rc
at the statement behind gives a witness of Rc at the statement in front. Then Rc may be laid beside
both relations of the law: the lost property stays as it is, so the errors are still paid once. What
Rc reads need not be common to the slots, and is in no key. -/
def LostBeside : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' Rc : S × F.E.Str → W → Prop) (act : BKey F S),
    p.LostBy on on' R R' act →
    (∀ a τ b w, on a → p.ior.red.out a τ = some b → on' b → Rc b w → Rc a (p.ext a τ w)) →
    p.LostBy on on' (fun a w => R a w ∧ Rc a w) (fun b w => R' b w ∧ Rc b w) act

/-! ## 6 The acting part that is meant -/

/-- The acting part of the shared chain at a place: the chain's own part of the carried record
(`get`); the stored table; and the columns of the trees with a number from lo to below hi. lo: the
number of the chain's first own tree. hi: the number of the first tree that is not yet sent at this
place. What the record holds beside the chain's own part (what was handed to the chain, which each
slot has of its own), and the trees of an earlier chain, are not in it. At the chain's first place
(hi = lo) it is the chain's own first record and the stored table. -/
def actAt {S₀ : Type} (F : Frame) (get : S → S₀) (lo hi : ℕ) : BKey F S :=
  ⟨S₀ × (oneExternalString (2 ^ F.a) SgX).Str × (ℕ → ℕ → Option (List UInt64)),
    fun a => (get a.1, a.2.1,
      fun j x => if lo ≤ j ∧ j < hi then (posL F.all j x).map a.2.2 else none)⟩

/-- A block that is typed at the chain's own part of the record and lifted (`Block.lift`), and whose
rounds open no tree with a number below lo, hands that acting part on. -/
def LiftHands : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (b₀ : Block S₀ Cl)
    (p : Piece C F S Cl W) (lo : ℕ),
    p.b = b₀.lift get set → (∀ t s, get (set t s) = s) →
    (∀ t s s', set (set t s) s' = set t s') → (∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) →
    p.HandsAct (actAt F get lo p.base) (actAt F get lo (p.base + p.trees))

/-- **The fold of lifted blocks is the fold of the blocks, laid back.** `get` and `set` obey two
laws of a part of a record: what was laid is got; what is laid last stays. An equation of the whole
verdict. -/
def FoldLift : Prop :=
  ∀ (S S₀ Cl : Type) (F : Frame) (name : String) (bs : List (Block S₀ Cl)) (back : List Fmt.RoundView)
    (get : S → S₀) (set : S → S₀ → S),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    ∀ (t : S) (v : Fmt.View),
      foldRun F name (bs.map (Block.lift get set)) back t v =
        (foldRun F name bs back (get t) v).map (set t)

/-- The number of the first tree that is not yet sent at place k of a row: the first own tree of the
block behind that place; behind the last block, the number behind its trees. -/
def hiAt : ℕ → Piece C F S Cl W → List (Piece C F S Cl W) → ℕ
  | 0, p, _ => p.base
  | _ + 1, p, [] => p.base + p.trees
  | k + 1, _, q :: l => hiAt k q l

/-- The acting parts that are meant, at the places of a row. -/
def actsOf {S₀ : Type} (get : S → S₀) (lo : ℕ) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) : ℕ → BKey F S := fun k =>
  actAt F get lo (hiAt k p l)

/-- At every block of a row the condition behind it, the relations and the extractor read the
statement through the acting parts alone. -/
def EachRels (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (act : ℕ → BKey F S) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.RelsBy (on (i + 1)) (R i) (R (i + 1)) (act i) (act (i + 1)) ∧ EachRels on R act (i + 1) l

/-- Every block's extractor keeps the carried claim Rc, at outputs inside the promise. -/
def EachKeeps (on : ℕ → S × F.E.Str → Prop) (Rc : S × F.E.Str → W → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    (∀ a τ b w, on i a → p.ior.red.out a τ = some b → on (i + 1) b → Rc b w →
      Rc a (p.ext a τ w)) ∧ EachKeeps on Rc (i + 1) l

/-- **The rule from the premise for one statement.** If the stretches tile the chain; every block
has `GoodIn` between its two places; every block is typed at the chain's own part of the record and
lifted, and no round opens a tree with a number below lo; the conditions, the relations R and the
extractors read a statement through the chain's own part of the record, the stored table and the
chain's own trees alone; and every extractor keeps the carried claim Rc: then the chain's decision
is a link with keys for a batch, between the relations "R and Rc", at the blocks' errors in a row,
each once. The key in front: the chain's own first record, the stored table, and the trees from lo
to below the first block's. -/
def ChainLinkOwn : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (name : String) (N : ℕ)
    (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (Rc : S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (h : (rowIOR p l).shape = uLT C (rowData p l)) (get : S → S₀) (set : S → S₀ → S) (lo : ℕ),
    Tiled p l → EachGoodIn on R 0 (p :: l) → EachRels on R (actsOf get lo p l) 0 (p :: l) →
    EachKeeps on Rc 0 (p :: l) → (∀ t s, get (set t s) = s) →
    (∀ t s s', set (set t s) s' = set t s') →
    (∀ q ∈ p :: l, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
    (∀ q ∈ p :: l, ∀ d ∈ q.ds, ∀ j ∈ d.opens, lo ≤ j) →
    LinkJ (foldRed name ((p :: l).map (·.b)) p l h) (shA _) N (actsOf get lo p l 0).2
      (actsOf get lo p l (1 + l.length)).2 (on 0) (fun a w => R 0 a w ∧ Rc a w)
      (Reduction.orOff (on (1 + l.length)) fun b w => R (1 + l.length) b w ∧ Rc b w)
      (rowExt d p l) (rowErr p l)

/-! ## 7 Do the statements elaborate where they are meant? -/

-- a block that is typed at a part of the record, lifted, goes in as it is; the keys at its places
example (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S)
    (b₀ : Block S₀ Cl) (base : ℕ) (ds : List RDT) (e : S × F.E.Str → Iop.Tr (uLT C ds) → W → W)
    (ε : Err (uLT C ds)) (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (N lo : ℕ) :
    Prop :=
  ((⟨b₀.lift get set, base, ds, [], e, ε⟩ : Piece C F S Cl W).bk on on' R R').LinkSh N
    (kkAt (actAt F get lo base))
    (kkAt (actAt F get lo
      (base + (⟨b₀.lift get set, base, ds, [], e, ε⟩ : Piece C F S Cl W).trees)))

-- the keys along a row of two, written out
example (act : ℕ → BKey F S) (kZ : BKey F S) (p q : Piece C F S Cl W) :
    keysBack act kZ 0 [p, q] = p.keyBack (act 0) (q.keyBack (act 1) kZ) := rfl

-- the premise of the rule at a row of one is the library's notion, as it is
example (N : ℕ) (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (p : Piece C F S Cl W) (kA kZ : BKey F S) :
    Keyed N on R 0 p [] kA kZ =
      (p.bk (on 0) (on 1) (R 0) (R 1)).LinkSh N (kkAt kA) (kkAt kZ) := rfl


end VerifiableInference.Desc.Sound
