-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/ReadsThereB.lean: FOR A FILE OF EVALUATIONS ALONG A WALK: THE Bool OF THE PUBLIC ITEM «K5.readsThere» (K5's files', through the table of joints' door): "what the caller's forms will name is there", ON THE FIRST CHAIN's RECORD ALONE. No Mathlib beneath it. It imports the record's type and the attention plan's alone: NOT Johnson/Desc/First/Batch/FormsIn.lean: its three small readers (the mask row's message's seat · "of the open segment's second sending") ARE TYPED OUT HERE, and Johnson/Desc/First/Att/Door/Law/ReadsThereTie.lean shows BY LEAN that the whole is u3AtB (Att/K05U3B.lean), which is typed over Johnson/Desc/First/Batch/FormsIn.lean's own.
  readsAtB own iU3 nW L F book: (tree) the ledger's array number iU3 has one own row and JUST nW columns (the kind's readers and the stated world count places by the number of columns, and the law wants the plan's) · (array) the link's list names at iU3 an array of the layout, of the open segment's second sending, with a row and at least nW columns · (mask) the segment's first message with mask rows is sent and sits at a seat of own.
  readsThereB W own s: that at an open attention segment, at the numbers iU3 | nW of the public record's plan of the segment's group (link / 2); false where no attention segment is open.
-/
import Johnson.Desc.First.State
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

def readsAtB (own : List (Nat × Nat)) (iU3 nW : Nat) (L : LinkCtx) (F : Fork) (book : OnBytes.TreeBook) : Bool :=
  ((F.trees[iU3]?).any fun T => T.R == 1 && T.K == nW) &&
    ((L.arrayOf[iU3]?).any fun b =>
      (reqArray L.check.rows.layout b.1 b.2).any fun Ar =>
        (b.1 == L.check.frame.link &&
          match (L.check.frame.shape.link[b.1]?).bind fun l => l.messages[Ar.message]? with
          | some m => m.moment == 1
          | none => false) && Decidable.decide (0 < Ar.sizeI) && Decidable.decide (nW ≤ Ar.sizeC)) &&
    (((((L.check.frame.shape.link[L.check.frame.link]?.map (·.messages)).getD []).findIdx? fun x =>
        x.shape.maskRows != 0).bind fun m => L.check.frame.whereIs L.check.frame.link m).bind fun o =>
      (book.place[o]?).bind fun x => if own.contains x then some x else none).isSome

def readsThereB (W : Verify.Public) (own : List (Nat × Nat)) (s : S) : Bool :=
  match s.here with
  | .att a => (W.A[a.L.link / 2]?).any fun p => readsAtB own p.iU3 p.nW a.L a.F s.book
  | _ => false

end H2K5.Door
