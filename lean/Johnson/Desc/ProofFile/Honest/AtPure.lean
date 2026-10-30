-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPure.lean: the honest prover of the proof file's own description
(`onlineDescription`) as one named term: the public part, the blank ground, the description, the whole book
of coins and the structure `Prover` (Honest/Frame.lean), computed from the three public files and
from one structure `OnlineProverParts`, which holds what is supplied of the kinds' parts, of the trace and of the
index committer. So every lemma, every test program and every statement can speak of one term, and
says at which `OnlineProverParts`. Executable definitions; no theorem.

  `OnlineProverParts`   the trace; the readers; the messages' data; the range; the encoded index's columns; the
     first chain's lots; the two later chains' prover's sides; what the parts pass on
  `OnlineProverParts.idle`   by name: no prover's side, no trace but the empty one, no column: the term
     type-checks with it
  `OnlineProverWithDescription`   what is computed
  `onlineProverFromPublicFiles`   the function that computes it. It returns an error with a message: where the public
     part, the blank ground, the description, the list of sendings or the function that builds the
     book return an error, where a test of the book fails (`bookWhole`), where a prover's side is at
     no place of its chain, and where the dummy is not in range. It puts no default in the place of
     a function that failed
  `OnlineProverWithDescription.stillIdle`   the lots without an honest side; the sub-protocols that send and have no
     prover's side

The types. Xi is the description's own instance `Inst`, Ky the table's key, and the key is
`pureKey`: these three are fixed here. The index W₀, the stored tables' pads and encoding randomness
Rc, the trace Tr and what the parts pass on are parameters of `OnlineProverParts`: the file that supplies the
real trace fixes them.

Limits.
  * Nothing is filled here. That the trace of a `OnlineProverParts` is a request's true trace, that its columns
    are the encoded index's, that its readers read that trace: each has to be proved by whoever
    supplies it.
  * The key's tie to the index committer's sample (`Committer.tie`, Honest/Committer.lean) is not
    asked here.
  * Which masked sumchecks are merges is guessed (`mergesByName`).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.ProofFile.Honest.RowData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

/-- **What other modules supply of the honest prover**, as fields. `trace`, `readers`, `rows`,
`enc`, `shared`, `second` and each lot's sides are functions of the public part; `inRange`, `dummy`,
`own₀`, `ownShared₀` and `meet` are not. -/
structure OnlineProverParts (W₀ Rc Tr X₀ X : Type) where
  /-- a request's trace; `none` where there is none -/
  trace : Pub → W₀ → Inst → Option Tr
  /-- the readers by which all parts read the witness, the index and the stored tables' pads and
  encoding randomness -/
  readers : Pub → W₀ → Rc → Tr → Readers
  /-- the data of the oracle messages' main rows: computed from the public part and the ground, as
  the prover's sides are; a function of the public instance -/
  rows : Pub → Ground → RowDataOf Inst
  /-- in range: a test on the index -/
  inRange : W₀ → Bool
  /-- a named element of the range -/
  dummy : W₀
  /-- the encoded index's column: by the statement's item and the position -/
  enc : Pub → W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)
  own₀ : X
  ownShared₀ : X₀
  meet : X → State (Common W₀ Rc OnBytes.TableKey) X₀ → X
  /-- the first chain's honest sides, lot by lot -/
  lots : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)
  shared : Pub → Ground → List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀)
  second : Pub → Ground → List (Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)

/-- **No prover's side; the empty trace at every request; no column.** Its readers return 0
everywhere, its data of the main rows is `RowData.empty`, every index is in range, and `meet`
returns its first argument. -/
def OnlineProverParts.idle : OnlineProverParts Unit Unit Unit Unit Unit :=
  { trace := fun _ _ _ => some ()
    readers := fun _ _ _ _ =>
      ⟨⟨fun _ _ _ _ => OnBytes.Slice.toF 0⟩, ⟨fun _ _ => OnBytes.Slice.toF 0⟩,
        fun _ => ⟨fun _ _ => OnBytes.Slice.toF 0, fun _ _ => OnBytes.Slice.toF 0⟩⟩
    rows := fun _ _ _ => RowData.empty
    inRange := fun _ => true, dummy := (), enc := fun _ _ _ _ _ => none
    own₀ := (), ownShared₀ := (), meet := fun x _ => x
    lots := [], shared := fun _ _ => [], second := fun _ _ => [] }

/-- **The honest prover at the proof file's own description.** -/
structure OnlineProverWithDescription (W₀ Rc Tr X₀ X : Type) where
  Z : Pub
  G : Ground
  F : FileDescription Inst
  B : ProverCoinCounts
  H : Prover W₀ Rc Inst OnBytes.TableKey Tr X₀ X
  readers : W₀ → Rc → Tr → Readers
  rows : RowDataOf Inst

variable {W₀ Rc Tr X₀ X : Type}

/-- **The function that builds it.** `o` stands for the format's second hash function, as in `onlineDescription`. -/
def onlineProverFromPublicFiles (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (P : OnlineProverParts W₀ Rc Tr X₀ X) :
    Except String (OnlineProverWithDescription W₀ Rc Tr X₀ X) :=
  (pubPlain o pol lay KL).bind fun Z =>
  (due? "the blank ground" (blankBy pureRoad.links Z)).bind fun G =>
  (onlineDescription o pol lay KL).bind fun F =>
  (Johnson.G.sendsOf pol lay KL).bind fun cs =>
  match cs with
  | [_, _, _, _, p0, p1, p2] =>
    (bookWhole F p0 p1 p2 (mergesByName F.first.blocksInOrder)).bind fun B =>
    let first := firstOf Z G P.lots
    let shared := P.shared Z G
    let second := P.second Z G
    if !(strays F.first.blocksInOrder first).isEmpty || !(strays F.shared.blocksInOrder shared).isEmpty ||
        !(strays F.second.blocksInOrder second).isEmpty then
      .error "a half stands at no place of its chain"
    else if !P.inRange P.dummy then .error "the dummy is not in range"
    else
      .ok
        { Z := Z, G := G, F := F, B := B, readers := P.readers Z, rows := P.rows Z G
          H := { stored := P.enc Z, trace := P.trace Z, key := pureKey, inRange := P.inRange
                 dummy := P.dummy, own₀ := P.own₀, ownShared₀ := P.ownShared₀
                 first := first, shared := shared, second := second, meet := P.meet } }
  | _ => .error "the list of sendings has not seven chains"

/-- **What is idle**: the lots of the first chain that have no honest side of their name;
then, chain by chain, the sub-protocols whose rounds send something and at whose place there is no
prover's side. -/
def OnlineProverWithDescription.stillIdle (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (P : OnlineProverParts W₀ Rc Tr X₀ X) :
    List String × List String × List String × List String :=
  (lotsLacking A.Z P.lots, lacking A.F.first.blocksInOrder A.H.first, lacking A.F.shared.blocksInOrder A.H.shared,
    lacking A.F.second.blocksInOrder A.H.second)

end ProofFile.Honest
